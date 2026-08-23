# Stage 3: kernel verification strategy

## Status: planning

The hardware model (Stages 1–2, 4, SSG-1 through SSG-9) is proven machine-side.
The next layer is the **kernel**: code that reads/writes `Machine` state and must
preserve invariants while doing so.

---

## 1. What we have

### Hardware side (proven, Rocq)

- **Coherence (S1):** unmap + flush → translate faults; missing flush is a provable
  leak. Leaf and non-leaf removal both proved.
- **Shootdown (S2):** N-core broadcast under weak memory (gpfsl iRC11) converges
  to the functional coherence theorems. IPI delivery model reifies the ghost steps.
- **IOMMU (S4):** IOTLB ⊆ mapping invariant maintained across VT-d/SMMUv3/AMD-Vi,
  including ATS device-TLB shootdown under weak memory.
- **Device models (SSG-3/5/6/7/8):** interrupt controller, timer, UART, NIC, disk
  — all generatable from Sail to Rocq with axiom-free test vectors.
- **MMU variants:** Sv39, MIPS PageGrain (1 KiB), LoongArch (odd/even pair),
  AArch64 (block+contpte+LPA2), custom inverted PT (satp 14/15, S=50 SLB).
- **Trust line (G1):** upstream `sail-riscv` pt_walk connected to our oracle via
  upstream bridge lemmas; bitfield extraction bridge validated.
- **Topology (SSG-1):** SMT harts, NUMA nodes, multikernel domains, boundary
  properties for page sharing.

### Kernel side (existing but unconnected)

- **Telix kernel** (`~/src/telix`, Rust): the kernel that controls the hardware.
  Has the page clustering (superpage/MMUPAGE/Zuteilungseinheit) allocator, COW
  fork, demand paging, the shootdown protocol implementation.
- **pgcl Linux patches** (`~/src/linux`, C): the original 2003+ ABI-compatible
  page clustering for 22 architectures with test harnesses.
- **Layer-A Lean proofs** (`~/src/tessera/property2/`): algorithmic proofs about
  KAU integrity, refcount discipline, allocation correctness — proved over an
  abstract memory model, not over the hardware `Machine`.

---

## 2. The verification gap

The gap is between the **kernel code** (Rust/C) and the **hardware model**
(Rocq/Sail). The kernel issues `sfence.vma`, modifies PTEs, sends IPIs, allocates
KAUs — and we need to know these operations preserve:

```
∀ core ∈ Machine.cores, ∀ entry ∈ core.tlb,
  ∃ pte ∈ Machine.mem such that entry.ppn = pte.ppn ∧ entry.perm ⊆ pte.perm
```

### The typical approach (and why it's hard)

1. Compile the kernel to a formal IR, give it a semantics in the prover
2. Prove the IR's behavior refines the specification
3. Trust (or verify) the compiler

This is what seL4, CertiKOS, and Asterinas do — and it's thousands of
person-years for a full kernel. We can't replicate that.

### Our shortcut: the protocol-is-the-proof

The insight from the hardware proofs: **the shootdown protocol itself enforces
coherence regardless of the kernel's internal logic.** The kernel could be buggy
in a thousand ways, but as long as it:

1. Marks the PTE invalid before sending IPIs
2. Sends IPIs to all cores that might have the TLB entry
3. Waits for all remote cores to acknowledge (with a release/acquire fence)
4. Only then reuses the physical frame

...the hardware model's `bc_broadcast_spec` theorem guarantees coherence. The
kernel's job is to **follow the protocol.** Verifying the kernel means verifying
it follows the protocol, not verifying every line of its allocator.

---

## 3. The incremental build-up

### Phase 3.1: Protocol contract extraction

**Goal**: For each kernel operation that modifies machine state, extract the
precise protocol contract — the minimal sequence of machine operations that
must be observed.

| Kernel operation | Protocol contract |
|-----------------|-------------------|
| `munmap` / `mprotect` downgrade | PTE invalid → sfence.vma local → IPI → wait ack |
| `madvise(MADV_DONTNEED)` | Same as munmap |
| COW break on write fault | Map new frame, flush old TLB entry |
| KAU split / merge | PTE cascade: invalidate, flush, IPI, wait |
| Page table free | TLB invalid for all entries in the subtree |
| IOMMU unmap | IOTLB invalidate → device-TLB invalidate (ATS) |
| `fork` | No shared TLB entries between parent and child |

These contracts are **finite-state-machine descriptions** that sit between the
kernel code and the hardware proofs.

### Phase 3.2: Contract-level proofs

**Goal**: Prove each protocol contract preserves the relevant hardware invariant,
using only the existing machine theorems.

Example for munmap:
```
Lemma unmap_protocol_preserves_coherence :
  ∀ (m : Machine) (va : vaddr),
    (* Pre: PTE valid for va in some core's TLB *)
    (∃ c e, e ∈ c.(tlb) ∧ e covers va) →
    (* Protocol: invalidate → flush → IPI_broadcast → wait_all *)
    let m' := ipi_broadcast (local_flush (invalidate_pte va m)) in
    (* Post: no core has a TLB entry for va *)
    ∀ c, ∀ e ∈ c.(tlb), ¬ (e covers va).
```

These proofs are **reusable lemmas** that any kernel implementation can invoke.
They don't depend on how the kernel allocates frames or manages page tables —
only on the protocol being followed.

### Phase 3.3: Kernel-PMC integration

**Goal**: Instrument the Telix kernel with Performance Monitoring Counter-style
assertions that the protocol is being followed at runtime.

This is the pragmatic bridge: instead of verifying the full kernel in Rocq,
we insert **lightweight assertions** that log protocol state transitions:

```rust
fn unmap_range(va: VirtAddr, len: usize) {
    invalidate_ptes(range);        // Step 1: mark invalid
    local_tlb_flush(range);        // Step 2: sfence.vma locally
    pmc_trace(PmcEvent::UnmapFlushDone { va, len });  // ← instrument
    send_ipi(range);               // Step 3: IPI broadcast
    wait_for_acks();               // Step 4: wait
    pmc_trace(PmcEvent::UnmapAcked { va, len });       // ← instrument
}
```

These traces can be checked **offline** against the protocol contracts from
Phase 3.2. A single test run that exercises all kernel operations provides a
witness that the protocol was followed for that test.

### Phase 3.4: Rust-to-Rocq extraction (long-range)

**Goal**: Extract a Rocq model of the kernel's protocol-relevant paths and
connect it to the machine model.

This is the "full verification" path, analogous to what Asterinas does with
its framekernel. The difference: we only extract the **protocol control flow,**
not the allocator, scheduler, filesystem, or driver logic. The extracted model
is perhaps 500–1000 lines of Rocq — small enough to prove manually.

### Phase 3.5: Cross-prover refinement (Lean ↔ Rocq)

**Goal**: Connect the Layer-A Lean proofs (KAUs, refcounts, allocation) to the
Rocq hardware model.

The Lean proofs say "if you follow the allocation discipline, refcounts are
sound." The Rocq proofs say "if you follow the shootdown protocol, TLBs are
coherent." The bridge: a **joint invariant** that says a KAU can only be freed
after the shootdown protocol completes. This is a paper proof that doesn't
require running both provers simultaneously.

---

## 4. What to do first

| Step | Effort | Payoff |
|------|--------|--------|
| **3.1 Protocol contracts** | ~1 week | Template for all downstream work |
| **3.2 Contract proofs** | ~2 weeks | Connects to hardware theorems; reusable |
| **3.3 Kernel-PMC instrumentation** | ~1 week | Can run on real hardware; catches regressions |
| **3.4 Rocq extraction** | ~4 weeks | Full formal connection; publishable result |
| **3.5 Cross-prover refinement** | ~2 weeks | Closes the Lean↔Rocq gap |

The recommended order: **3.1 → 3.2 → 3.3** gives us a concrete deliverable
(a kernel that traces and verifies its own protocol compliance) in ~4 weeks.
Steps 3.4 and 3.5 are the deep-verification tail that provide the strongest
guarantees.

---

## 5. Relationship to existing kernel code

### Telix

The Telix kernel in `~/src/telix/` already implements the shootdown protocol,
page clustering, COW, and the KAU allocator. The PMC instrumentation (Step 3.3)
can be added without structural changes — just trace points.

### pgcl Linux

The pgcl patches in `~/src/linux/` implement the same protocol for 22
architectures. The protocol contracts (Step 3.1) apply identically. The Linux
PMC infrastructure (`perf`) can carry the same traces.

### QEMU test harness

The QEMU tests (`test-invpt.S`, `test-slbmode15.S`) exercise the hardware model
directly. A kernel-level test suite that boots Telix in QEMU with protocol
tracing enabled provides end-to-end validation.

---

## 6. Open questions

1. **Which prover for the kernel model?** Rocq (same as hardware) or Lean
   (same as Layer-A)? Rocq is the natural choice since the machine model lives
   there, but the Lean→Rocq bridge could go either direction.

2. **How much of the kernel to extract?** Only the page table manipulation and
   shootdown protocol, or also the allocator and COW logic? The protocol-only
   approach (Step 3.4) keeps the extracted model small.

3. **Is the Rust type system sufficient?** Rust's ownership model already
   prevents many classes of bugs (use-after-free, data races). Combined with
   the hardware coherence proofs, the remaining gap is: does the kernel follow
   the protocol? Rust can't answer that on its own, but the PMC traces can.
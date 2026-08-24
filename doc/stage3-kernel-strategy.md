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

- **Telix prototype** (`~/src/telix`, Rust): the original monolithic
  implementation controlling hardware. Has page clustering
  (superpage/MMUPAGE/Zuteilungseinheit) allocator, COW fork, demand paging, the
  shootdown protocol implementation.
- **Telix redesign** (`~/src/telix-whitepaper/`): a ground-up rearchitecture
  specified in a design proposal. Key structural changes from the prototype:
  - **Framekernel + Multikernel hybrid** (the "matryoshka" control plane):
    within a NUMA node → framekernel (Asterinas-style shared address space, CPS
    state machines); between NUMA nodes → multikernel (Barrelfish-style message
    passing).
  - **External pagers**: virtual memory management hoisted out of the kernel
    into privileged userspace servers. The kernel provides primitives (PTE
    manipulation, TLB shootdown, page-table subtree sharing); userspace composes
    them into allocation/COW/page-cache strategies.
  - **Coremapless physical memory**: no global `mem_map[]` descriptor array.
    Physical frames quantized by $Z$ act as their own handles; metadata is
    allocated dynamically within the subsystems that need it. Backed by an
    LLFree lock-free allocator for cache-line-friendly allocation.
  - **Continuation-passing style within framekernel**: all in-kernel execution
    is interrupt-driven state machines (Rust `Future` continuations). Kernel→user
    transitions go through FlexSC/io_uring completion rings.
  - **Personality servers in userspace**: Linux, Windows, Zircon, OpenHarmony
    ABIs implemented as isolated userspace servers, not in-kernel subsystems.
- **pgcl Linux patches** (`~/src/linux`, C): the original 2003+ ABI-compatible
  page clustering for 22 architectures with test harnesses.
- **Layer-A Lean proofs** (`~/src/tessera/property2/`): algorithmic proofs about
  KAU integrity, refcount discipline, allocation correctness — proved over an
  abstract memory model, not over the hardware `Machine`.

### The Rust → Rocq verification pipeline (available toolchain)

There is an active, production-quality toolchain for connecting Rust code to
Rocq/Coq proofs. The following tools have reached maturity (2024–2025):

| Tool | Group | Approach | Maturity |
|------|-------|----------|----------|
| **RustBelt** | MPI-SWS (2018) | Iris soundness proof for Rust's type system. Foundation, not a program verifier. | Published, stable |
| **RefinedRust** | MPI-SWS (2024) | Translates Rust MIR → Coq; proves functional correctness in Iris. *RustBelt's successor for program verification.* | Published, active |
| **Aeneas** | Inria | Translates Rust (incl. `unsafe`) → Coq; suited for crate-level verification | Active |
| **Creusot** | Inria | Deductive verification via Why3; SMT-backed, not Coq | Active |
| **Verus** | VMware/Community | SMT-based (Z3), annotation-driven; no Coq connection | Active, most ergonomic |
| **Rocq-of-Rust** | Formal Land | Direct Rust → Rocq translation; targets smart-contract and system code | New (2024–25) |

**RefinedRust was the initial candidate** for Telix because it embeds
into **Iris** — the same separation logic that Tessera's hardware proofs use
(`shootdown_iris.v`, gpfsl weak-memory proofs) — and handles real (surface)
Rust, including `unsafe` blocks.

However, after further analysis (documented in the whitepaper's verification
chapter, §Toolchain Selection), **manual Iris heap_lang was chosen instead**.
The reason: RefinedRust and Aeneas assume the standard library memory model
and have not been tested on bare-metal kernel code (no `std`, raw MMIO,
inline assembly, custom allocator).  The adaptation burden is unbounded
toolchain risk; the manual Iris approach has a bounded, auditable semantic
gap (the Iris program is read and audited, not a compiler pipeline whose
translation correctness must itself be proved).  This is the same decision
seL4 made (manual Isabelle specification rather than an automatic
C-to-Isabelle translator), for the same reason.

The tool survey above is retained as rationale for *why* manual Iris was
chosen: each automatic tool was considered and rejected for specific reasons.

The missing piece is **not** a tool — it is a discrete, well-scoped layer of
~2,000 lines of Rocq: **the machine interface Iris layer** (see §3.4).

---

## 2. The verification gap

The gap is between the **kernel code** (Rust) and the **hardware model**
(Rocq/Sail). The kernel issues `sfence.vma`, modifies PTEs, sends IPIs, allocates
KAUs — and we need to know these operations preserve:

```
∀ core ∈ Machine.cores, ∀ entry ∈ core.tlb,
  ∃ pte ∈ Machine.mem such that entry.ppn = pte.ppn ∧ entry.perm ⊆ pte.perm
```

### The toolchain connection: both sides already speak Iris

The Tessera hardware proofs use Iris separation logic (the `shootdown_iris.v`
family). The kernel's behaviour is specified by hand in Iris heap_lang (the
same separation logic, same proof assistant). This means:

```
Telix (Rust)  ──manual Iris spec──►  Coq/Iris model of kernel  ──compose──►  Machine (Tessera)
                                          │                                      │
                                          │  Iris separation logic               │  Iris separation logic
                                          │  (memory ownership,                  │  (TLB ownership,
                                          │   page-table authority)              │   weak memory, IOMMU)
                                          └──────────────┬───────────────────────┘
                                                         │
                                               Same proof assistant
                                               Same separation logic
                                               Different invariants → same composition
```

A kernel function like `unmap_range()` gets an Iris spec:
```
{ TLB_entry(va) ∗ PTE_valid(va) }  unmap_range(va)  { ¬TLB_entry(va) ∗ ¬PTE_valid(va) }
```

The hardware's `bc_broadcast_spec` theorem guarantees that following the
shootdown protocol achieves `¬TLB_entry(va)`. The manual Iris proof shows the
kernel follows the protocol. The two proofs **compose**.

### The limitation: kernel Rust ≠ normal Rust

Kernel code has no `std`, uses raw MMIO, executes assembly (`sfence.vma`,
`mret`), and uses a custom allocator (LLFree, no global `Box`). Tools like
RefinedRust and Aeneas assume the standard library memory model and have not
been tested on bare-metal kernel code. This is the primary reason manual Iris
was chosen over automatic translation: the semantic gap between an Iris
heap_lang spec and the Rust implementation is a single text that is read and
audited, not a compiler pipeline whose translation correctness must itself be
proved. The adaptation burden is well-scoped (~3–6 months of Rocq work to
define the machine interface layer).

### The redesign makes verification easier

Each whitepaper design choice reduces verification surface area:

| Design choice | Verification benefit |
|--------------|---------------------|
| **External pagers** (VM in userspace) | Each pager is a separate process with its own Iris proof; faults are bounded |
| **Coremapless** (no global page array) | No global invariant over all frames; per-frame ownership via LLFree tokens |
| **Continuation-passing style** | State machines have finite, explicit states — easier to specify than arbitrary stackful code |
| **Personality servers** | Foreign ABIs are untrusted; correctness depends only on capability channel protocols, not ABI internals |
| **Framekernel shared address space** | No address-space switch during IPC; TLB coherence is the *only* cross-domain concern |

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

### Phase 3.4: Machine interface Iris layer

**Goal**: Define the Iris resources and specifications that form the contract
between kernel code and hardware model.

This is the critical enabling layer — ~2,000 lines of Rocq that define:

```coq
(* Core Iris resources for the machine interface *)

(* "I own this PTE and it maps va → pa" *)
Definition pte_token (va : vaddr) (pa : paddr) (perm : Perm) : iProp Σ := ...

(* "I flushed this TLB entry; it's gone from all cores" *)
Definition tlb_flushed (va : vaddr) : iProp Σ := ...

(* "The IOMMU domain d translates va → pa" *)
Definition iommu_mapping (d : Domain) (va : vaddr) (pa : paddr) : iProp Σ := ...

(* "This PTE subtree is shared across N address spaces (shared page tables)" *)
Definition shared_subtree (root_ppn : paddr) (n : nat) : iProp Σ := ...

(* Spec for the sfence.vma instruction *)
Lemma wp_sfence_vma (va : vaddr) :
  {{{ pte_token va pa perm ∗ ... }}}
    sfence_vma va
  {{{ RET (); tlb_flushed va }}}.

(* Spec for the unmap protocol, composing the hardware theorems *)
Lemma unmap_protocol_preserves_coherence (m : Machine) (va : vaddr) :
  pte_token va pa perm ∗ tlb_entry va ⊢
  |==> tlb_flushed va ∗ ¬pte_token va pa perm.
```

This layer only needs to be written **once**. Every kernel function then
inherits these resources. The existing Tessera theorems (`bc_broadcast_spec`,
`iommu_shootdown_correct`, etc.) prove that the hardware semantics genuinely
satisfy these Iris specifications.

### Phase 3.5: Manual Iris kernel proofs

**Goal**: Specify the framekernel core's protocol-relevant paths by hand in
Iris heap_lang and prove they satisfy the machine interface Iris layer from
Phase 3.4.

This is the chosen path (not RefinedRust; see §1 above and the whitepaper's
verification chapter). The kernel's behaviour is modelled by hand, in the style
of seL4's Isabelle specification:

1. **Specify** each kernel function (page-table manipulation, TLB shootdown,
   IPI send/receive, IOTLB invalidate) as an Iris heap_lang program with
   pre/post-conditions from the machine interface layer (Phase 3.4)
2. **Prove** that each function satisfies its machine interface spec
3. The hardware theorems guarantee that satisfying the specs implies coherence

Target scope: the protocol-relevant code paths only — PTE walk/modify,
`sfence.vma`, IPI send/receive, IOTLB invalidate. Not the allocator, scheduler,
filesystem, or personality servers.

Estimated Iris model: 500–1,000 lines of Rocq (hand-written, not extracted).

**Parallel track for external pagers**: Each pager (userspace VM server) gets
its own manual Iris proof. The pager's spec is "if the kernel gives me PTE
ownership, I will manage COW/faults correctly." Since pagers are isolated
processes, their proofs are independent and can be developed incrementally.

### Phase 3.6: Cross-prover refinement (Lean ↔ Rocq)

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
| **3.4 Machine interface Iris layer** | ~3 months | The connecting piece: Iris resources for kernel↔hardware |
| **3.5 Manual Iris kernel proofs** | ~3 months | Prove kernel satisfies machine interface specs |
| **3.6 Cross-prover refinement** | ~2 weeks | Closes the Lean↔Rocq gap |

The recommended order: **3.1 → 3.2 → 3.3** gives us a concrete deliverable
(a kernel that traces and verifies its own protocol compliance) in ~4 weeks.
**3.4** is the critical path for deep verification — it defines the Iris
resources that both the manual Iris kernel proofs (3.5) and the hardware
theorems consume.
**3.5** then hand-writes the Iris heap_lang specs and proves them against 3.4.
**3.6** closes the Lean↔Rocq gap.

---

## 5. Relationship to existing kernel code

### Telix prototype (`~/src/telix/`)

The existing prototype implements the shootdown protocol, page clustering, COW,
and the KAU allocator as a monolithic kernel. The PMC instrumentation
(Phase 3.3) can be added directly — the protocol operations are the same
regardless of architectural style.

### Telix redesign (whitepaper)

The redesign splits the prototype's monolithic VM into:

- **Framekernel core**: owns page tables, executes `sfence.vma`, sends IPIs,
  manages the LLFree allocator. ~3,000–5,000 lines of Rust with `unsafe` for
  MMIO and privileged instructions.
- **External pagers**: userspace servers that handle COW faults, ZFOD, page cache,
  KAU split/merge decisions. Each pager runs in its own address space and
  communicates with the framekernel via FlexSC/io_uring completion rings.
- **Personality servers**: Linux/Windows/Zircon/OpenHarmony ABI emulation as
  isolated userspace processes.

Verification implications:
- The **framekernel core** is the only part that needs deep verification
  (manual Iris heap_lang + machine interface Iris layer). It's small and well-bounded.
- **External pagers** each get their own, independent proofs. A bug in the Linux
  personality server cannot corrupt the framekernel or other pagers.
- **Capability channels** between components can be verified at the protocol
  level (Phase 3.2) without verifying the internal logic of any server.

### pgcl Linux

The pgcl patches in `~/src/linux/` implement the same protocol for 22
architectures. The protocol contracts (Phase 3.1) apply identically. The Linux
PMC infrastructure (`perf`) can carry the same traces.

### QEMU test harness

The QEMU tests (`test-invpt.S`, `test-slbmode15.S`) exercise the hardware model
directly. A kernel-level test suite that boots Telix in QEMU with protocol
tracing enabled provides end-to-end validation.

---

## 6. Open questions

1. **Which prover for the kernel model?** Rocq (same as hardware) is the natural
   choice since the machine model lives there and Iris is the shared language.
   The Lean↔Rocq bridge (Phase 3.6) can connect the Layer-A KAU proofs either
   direction.

2. **How much of the kernel to extract?** Only the framekernel core — page table
   manipulation, TLB shootdown, IPI protocol, IOTLB invalidate. The external
   pagers, personality servers, and filesystem are untrusted or separately
   verified.

3. **Is the Rust type system sufficient?** Rust's ownership model already
   prevents many classes of bugs (use-after-free, data races). Combined with
   the hardware coherence proofs, the remaining gap is: does the kernel follow
   the protocol? Rust can't answer that on its own — the manual Iris heap_lang
   specification closes the gap by hand-writing the kernel's behavioural spec
   and proving it against the machine interface resources.

4. **How does the framekernel's continuation-passing style interact with
   verification?** CPS state machines have explicit, finite state sets — this is
   a *benefit* for verification (no unbounded stack frames to reason about).
   Rust `Future` combinators have known Iris models from the RustBelt project.

5. **How do we handle the LLFree allocator in Iris?** The allocator is a
   concurrent data structure with lock-free CAS operations. Verifying it in Iris
   is a known problem (
   ["Iron"](https://iris-project.org/pdfs/2021-popl-iron.pdf) for persistent
   data structures). Alternatively, LLFree can be treated as a trusted primitive
   and only the *protocol* of allocation/deallocation is verified.

6. **Does QEMU's Sail-generated model serve as a test oracle for the kernel?**
   Yes — the upstream `sail-riscv` pt_walk can be linked into our conformance
   bridge (see `upstream_walk_conformance.v`). A QEMU build with Sail-generated
   TLB logic can act as a diff-test oracle: run the kernel, capture all page
   walks, and compare against Tessera's oracle_walk for conformance.
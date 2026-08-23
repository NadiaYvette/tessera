# Tessera — Machine Model Reference

**For kernel verification against an integrity-guaranteed hardware model.**

This document describes the full machine model assembled across `hardware/src/*.sail`
and proved over in `hardware/rocq/*.v`. It is the hardware-side foundation for the
kernel verification: every kernel invariant about machine state must be expressible
in terms of the types and operations defined here.

## 1. Why this document exists

The kernel (`~/src/telix/` and, via pgcl, `~/src/linux/`) manages hardware state:
page tables, TLBs, the IOMMU, interrupt controllers, timers, devices. To *prove*
the kernel maintains that state's integrity, the verification must have a
machine-checked model of what that state *is* and what operations the hardware
performs on it.

Tessera provides exactly that: a **Sail model** of the machine (the specification)
from which **Rocq types** are mechanically generated, and **Rocq proofs** (~53 files,
~722 axiom-free checks) establish what the hardware guarantees. This document is the
reference for a kernel verifier: "what state is the hardware in, and what theorems
are already proved about it?"

## 2. The machine state

The full machine state (`Machine` in `hardware/src/machine.sail`) is a single record
containing everything the kernel cares about:

```
Machine
├─ cores   : list Core           — all CPUs/cores
├─ mem     : PageTable           — page tables in physical memory
├─ ram     : Ram                 — data memory (byte-addressable)
├─ ipi     : list bool           — per-core IPI mailbox
├─ iotlb   : list IotlbEntry     — IOMMU translation cache
├─ devtlbs : list DevTlbEntry    — device-side TLBs (ATS)
├─ prireqs : list PriRequest     — PRI page fault requests
├─ ioqueue : list InvalidationCmd — IOMMU queued invalidation commands
├─ stes    : list Ste            — SMMUv3 stream table entries
└─ cds     : list Cd             — SMMUv3 context descriptors
```

### 2.1 Core (CPU)

Each core has:

| Field | Type | Meaning |
|-------|------|---------|
| `satp_ppn` | `bits(44)` | Root page-table physical page number |
| `tlb` | `list TlbEntry` | Per-core software-visible TLB |
| `hart` | `int` | SMT thread id (within a physical core) |
| `node` | `int` | NUMA node id |

The `hart` and `node` fields are the **SSG-1 topology plumbing** — they exist to
attach future topology-aware theorems (SMT co-residency, NUMA locality) but no
current proof depends on them.

### 2.2 Page table memory

`PageTable = list MemEntry` where each `MemEntry` is `{addr: paddr, pte: Pte}`.
Page tables live here; the walk reads PTEs by physical address. A missing address
means the translation faults.

**Pte** (the page table entry leaf view):
```
{ valid, read, write, exec, user : bool
; napot : bool      — Svnapot N-bit (64 KiB NAPOT pages)
; ppn   : bits(44)  — physical page number
}
```

### 2.3 Data RAM

`Ram = list Byte` where each `Byte` is `{addr: paddr, data: bits(8)}`. Byte-
addressable physical memory for data loads/stores. Separate from the PTE memory
(they are logically one physical address space but modeled as two association lists
for the translation vs. data distinction). A missing address means a fault.

Address decode routes accesses: `Region = RAM | MMIO`. The `read_byte`/`write_byte`
functions decode the address and dispatch accordingly.

### 2.4 TLB entry

```
TlbEntry {
  vaddr : vaddr      — full VA the entry was filled for (VIVT/VIPT index/tag)
  vpn   : bits(27)   — Sv39 VPN = VA[38..12]
  ppn   : bits(44)   — physical page number
  perm  : Perm       — None_ | Read | ReadWrite
  napot : bool       — whether this is a 64 KiB NAPOT entry
}
```

The `vaddr` field (the full VA, not just the VPN) is the **per-cell coupling** —
essential for VIVT/VIPT architectures where the set-index bits live in the page
offset, which the VPN discards. For PIPT/RISC-V, it's degenerate (vaddr maps to
VPN); for VIVT/VIPT, it carries the real tag.

### 2.5 Permissions

```
Perm = None_ | Read | ReadWrite
```

(Execute is a separate PTE bit modeled but not part of the permission translation
— the walk faults on X=1 independently.)

### 2.6 IOMMU (SSG-4)

**IotlbEntry**: the IOMMU's translation cache entry (the "IOTLB"):
```
{ did: int, pasid: int, iova: vaddr, pa: paddr, perm: Perm, gen: int }
```

**DevTlbEntry**: a device's own translation cache (ATS device-TLB):
```
{ did: int, iova: vaddr, pa: paddr, perm: Perm }
```

**PriRequest**: a PRI page fault request (device asks kernel to map a page):
```
{ did: int, pasid: int, iova: vaddr, pending: bool }
```

**InvalidationCmd**: a queued invalidation descriptor (VT-d / SMMU / AMD-Vi):
```
{ is_wait: bool, gran: InvalidationGran, va: vaddr, did: int, pasid: int }
```

**Ste** (SMMUv3 Stream Table Entry) and **Cd** (Context Descriptor) carry the
stage-1/stage-2 table roots for SMMUv3 two-stage walks.

**Invariants proved**:
- `IOTLB ⊆ mapping` (IOMMU coherence): after `iotlb_invalidate`, no IOTLB entry
  translates a freed frame
- `iommu_shootdown_correct`: IOMMU shootdown re-establishes coherence
- Queued-invalidation correctness: `iommu_shootdown_via_queue_correct`
- ATS correctness: `iommu_shootdown_ats_correct`
- VT-d, SMMUv3, AMD-Vi platform variants all proved
- PASID-cache coherence (generation tags, eviction, refill)
- Weak-memory lifts (gpfsl) for all IOMMU/ATS/PRI/PASID translation loops

### 2.7 Interrupt controller (SSG-3)

Modeled as a separate Sail file (`intc.sail`) integrated with the machine. The
controller has per-interrupt pending bits, masking, per-hart delivery gates,
and priority selection. Proved:

- `intc_send_ack_refines_deliver_ipi`: the controller's send+ack produces the
  same mailbox as `deliver_ipi`
- `intc_delivery_enables_receive_ipi`: a controller-produced mailbox flushes
  exactly the target core
- Priority selection (`topei`) soundness, minimality, completeness
- Masking + interrupt context (pend while in context, deliver on exit)

### 2.8 Timer device (SSG-5)

Per-hart `mtime` / `mtimecmp` registers. Proved: multi-hart isolation, overflow,
ack-target isolation, monotonicity. 5 headline theorems + 18 test vectors.

### 2.9 UART (SSG-6)

8250/16550 register set (`write_thr`, `tx_complete`, `read_rbr`). Proved: Tx
round-trip, flow-control, interrupt readiness. 15 test vectors.

### 2.10 Network device (SSG-7)

DMA descriptor ring (`DmaDesc`, `NetRegs`). Proved: ring wraparound, TX/RX
independence, **DMA coherence via SSG-4 IOMMU** (`net_dma_coherence.v`). 12 test
vectors + 4 DMA coherence test vectors.

### 2.11 Disk device (SSG-8)

Disk command/completion rings (`DiskCmd`, `DiskRegs`). Proved: flush/barrier
identification, cmd/cmp independence. 20 test vectors.

## 3. MMU translation: the four variants

Translation is architecture-pluggable. The machine skeleton is architecture-agnostic;
each MMU variant supplies walk/refill/flush/lookup semantics behind the same
interface. Four variants exist:

### 3.1 RISC-V Sv39 (hardware walker)

The reference variant. Three-level radix-tree page table walk (`translate` →
`walk_decision` at each level → `leaf_addr` at the leaf). PTE leaf interpretation
includes the Svnapot N-bit for 64 KiB NAPOT pages. `sfence_vma_all` /
`sfence_vma_va` for TLB invalidation.

**Generated from** `machine.sail` lines 1-230 (the core walk + PTE types + VPN
extraction) plus the TLB operations (lines ~231-340).

### 3.2 MIPS software-refill (PageGrain)

The kernel's refill handler is *our code*, so its correctness is a theorem, not a
trusted assumption: `mips_refill_lookup_covers` proves refill-then-lookup yields
the entry's translation when the entry covers the address. Includes:

- **PageGrain ESP**: 1 KiB page support (`K=256B`, the VPN2X field at
  `EntryHi[12:11]`)
- **PageMask**: run-of-1s decode (the `{4^k·M}` spectrum), even count only
- `pfn_shift = 10` under ESP (vs. 12 standard)
- **QEMU oracle diff-test**: `compute_mask_level_conforms` against
  `~/src/QEMU` branch `nadia.chambers/page-grain-001`, 16 diff vectors
- Coherence/shootdown twins proved

Sail source: `hardware/src/mips_tlb.sail`; generated into `hardware/rocq/mips_tlb.v`.

### 3.3 LoongArch software-refill

Software-refill like MIPS, but with LoongArch-specific features:

- **Per-entry `ps` page shift** (not MIPS's PageMask decode)
- **Odd/even pair**: an entry covers two adjacent pages of size `2^ps`;
  VPPN = `VA[47:13]`; PA = `pfn[35:ps-12] @ va[ps-1:0]` with `va[ps]` selecting
  pfn0/pfn1

Coherence/shootdown twins proved. QEMU differential oracle pinned against
`loongarch_tlb_search_cb`/`loongarch_map_tlb_entry`/`loongarch_check_pte`.

Sail source: `hardware/src/loongarch_tlb.sail`; generated into `hardware/rocq/loongarch_tlb.v`.

### 3.4 AArch64 VMSAv8-64 (hardware walker)

The richest page-size menu. Features:

- **Block descriptors**: a level < 3 descriptor is a superpage
- **Contiguous bit (CONT)**: extends the page by `ContiguousSize` extra address bits
- **LPA2** (DS2 16-byte descriptor encoding)
- **TLBI-by-VA** (the AArch64 TLB invalidation analog of SFENCE.VMA)

The AArch64 fragment (`sail_arm_tlb.sail`) is transcribed **verbatim** from the
upstream `sail-arm` model's `v8_base.sail` `ContiguousSize`/`TGxGranuleBits`/
`TranslationSize`/`StageOA` — the only non-hand-written MMU variant.

Sail source: `hardware/src/aarch64_tlb.sail`, `hardware/src/sail_arm_tlb.sail`.

### 3.5 Custom RISC-V inverted page table (satp modes 14/15)

A forward-looking custom extension: **partner-hashed inverted page tables** with
a 56-size superpage spectrum (`g_n = K × 2^(W×n)`, K=256B, W=1, n ∈ [0,55]).

Features:
- **Partner hashing** (BKZ-style): additive fold of sp_vpn + partition, linear probe,
  O(1) amortized with no rehashing
- **SLB** (Segment Lookaside Buffer): POWER9-style 256-entry segment cache
- **Residue-based TLB partitioning**: partition = `size_log2 mod 4`, so each TLB
  partition spans the full size spectrum (avoids Intel's fixed-reach trap)
- **PhiPT**: the full inverted page table with linear probing over all 56 sizes,
  largest-first (Zipf-order)

#### SLB design: S=50 segment boundary

The SLB matches on the **VA segment ID** — the top bits of the virtual address.
The split point S determines both segment size and VSID width:

```
VA = [63 : S] [S-1 : 0]
     VSID      intra-segment
```

| Parameter | Old (S=28) | New (S=50) | Rationale |
|-----------|-----------|-----------|-----------|
| Segment size | 256 MiB | 16 PiB | Must exceed max superpage (64 TiB) |
| VSID bits | 36 | 14 | Still 16,384 segments; 256-entry SLB never thrashes |
| Max segments | 68B | 16,384 | Typical process uses 2–5; namespace exhaustion impossible |

**Why S=50 specifically:**

1. **Superpage containment**: the max superpage is 64 TiB (size_log2=46). A segment
   must be ≥ max superpage to avoid a single superpage crossing multiple SLB entries
   with potentially conflicting VSIDs. S=50 (16 PiB) comfortably exceeds 64 TiB.

2. **POWER reference**: IBM POWER supports 256 MiB and 1 TiB segments. Linux
   normally uses 256 MiB, but the 1 TiB option exists precisely for large-memory
   workloads where the SLB would otherwise thrash. Our 16 PiB segments are the
   logical endpoint of that trajectory: large enough that segmentation *never*
   fragments.

3. **VSID headroom**: 14 bits = 16,384 segments. POWER hardware has only 32–64 SLB
   entries yet a single process uses 2–5 active segments. Even with petabyte-scale
   address spaces and hundreds of concurrent processes, 16K segments won't be
   exhausted. The remaining bits are available for ASID multiplexing.

4. **64-bit VA**: unlike architectures that truncate at 48 or 57 bits, the inverted
   PT has no radix-tree cost for wide virtual addresses. Full 64-bit VAs are natural.

**SLB entry layout:**

```
word0[0]      = valid
word0[1]      = global
word0[5:2]    = perms (R/W/X/U bits)
word0[9:6]    = size (4 bits, for forward-compat)
word0[29:10]  = PPN (20 bits, placeholder)
word1[13:0]   = VSID (14-bit segment identifier)
word1[29:14]  = ASID (16-bit address-space ID)
word1[63:30]  = reserved
```

**Translation path (mode 15):** TLB lookup → SLB lookup (gating step) → PHIPT
probe (all 56 sizes, largest first) → TLB fill. Mode 14 skips the SLB and goes
directly to the PHIPT.

## 4. Proven theorems about machine state

### 4.1 Coherence: "no stale translations" (Stage 1 + 1.1)

| Theorem | File | Meaning |
|---------|------|---------|
| `unmap_correct` | `coherence.v` | Unmap + flush → translate faults; TLB empty for that VA |
| `unmap_without_flush_breaks_coherence` | `coherence.v` | Unmap without flush → stale TLB entry survives |
| `unmap_leaf_correct` | `coherence_leaf.v` | Same for leaf (level-0) removal |
| `unmap_leaf_without_flush_breaks_coherence` | `coherence_leaf.v` | Same gap for leaf removal |

These are the §4 crux: "a missing flush is a provable error."

### 4.2 Shootdown: "all cores agree" (Stage 2)

| Theorem | File | Meaning |
|---------|------|---------|
| `shootdown_correct` | `shootdown.v` | Sequential N-core shootdown → all cores coherent |
| `broadcast_spec` | `shootdown_iris.v` | Iris HeapLang concurrent broadcast refines the pure shootdown |
| `bc_broadcast_spec` | `shootdown_weak_broadcast.v` | N-core broadcast under weak memory (gpfsl/ORC11) |
| `ipi_broadcast_correct` | `ipi.v` | IPI-based protocol (deliver+receive) refines the functional shootdown |
| `bc_broadcast_intc_spec` | `shootdown_weak_broadcast_intc.v` | Full controller-in-the-loop weak-memory shootdown |

### 4.3 IOMMU: "devices can't reach freed frames" (Stage 4)

| Theorem | File | Meaning |
|---------|------|---------|
| `iommu_coherent` | `iommu_proofs.v` | IOTLB ⊆ mapping invariant is maintained |
| `iommu_shootdown_correct` | `iommu_proofs.v` | IOMMU shootdown re-establishes coherence |
| `iommu_shootdown_via_queue_correct` | `iommu_proofs.v` | Queued-invalidation IOMMU shootdown |
| `iommu_shootdown_ats_correct` | `iommu_proofs.v` | ATS device-TLB shootdown |

All axioms-free, all three platforms (VT-d/SMMUv3/AMD-Vi), all weak-memory-lifted.

### 4.4 Cross-arch coverage

Every MMU variant has its coherence/shootdown twins proved:
- MIPS: `mips_flush_clears`, `mips_unmap_without_flush_breaks_coherence`,
  `mips_refill_flush_composes`, `mips_shootdown_correct`
- LoongArch: `la_flush_clears`, `la_unmap_without_flush_breaks_coherence`,
  `la_refill_flush_composes`, `la_shootdown_correct`
- AArch64: `aa_flush_clears`, `aa_unmap_without_flush_breaks_coherence`,
  `aa_refill_flush_composes`, `aa_shootdown_correct`
- RISC-V inverted PT: `phi_tlb_flush_clears`, `phipt_invalidate_removes`,
  `phipt_translate_composed` (+ 15 coherence proofs, 7 SLB test vectors)

## 5. How the kernel's invariants connect

The kernel's central invariant is **TLB ⊆ page table** (every cached translation
is backed by a valid PTE in memory). The machine model gives this precise form:

```
∀ core ∈ Machine.cores, ∀ entry ∈ core.tlb,
  ∃ pte ∈ Machine.mem such that
    entry.ppn = pte.ppn ∧ entry.perm ⊆ pte.perm
```

The Stage 1/1.1 coherence theorems prove this invariant is **maintained by
unmap+flush** and **violated by unmap without flush**.

The kernel's **shootdown protocol** (unmap → sfence local → IPI broadcast →
wait for acks → frame free) is exactly what the Stage 2 theorems prove correct:
after the protocol, **every core's TLB is empty for the unmapped VA** (the
stronger post-condition that implies coherence).

The kernel's **IOMMU invariant** (IOTLB ⊆ page table) is exactly what the Stage 4
theorems prove: after `iotlb_invalidate`, no IOTLB entry translates the freed
frame. The queued-invalidation command-queue model mirrors the real VT-d/SMMUv3/
AMD-Vi hardware interface.

## 6. Trust boundaries

### What is machine-checked proof

Every `.v` file in `hardware/rocq/` is a **Rocq proof** — checked by `rocq compile`,
each `Qed` verified, with `Print Assumptions` enforced by `build.sh`. All 646+
non-weak and 76+ weak proof obligations are axiom-free.

### What is a hand-written model (the trust gap)

The Sail source files (`hardware/src/*.sail`) are **hand-written**, not mechanically
derived from upstream Sail ISA models. This is the primary trust-line gap (G1 in
`rigor-trust-line.md`):

- The RISC-V Sv39 walk is a hand transcription, not linked to upstream `sail-riscv`
- The MIPS and LoongArch variants have no upstream Sail models at all
- The AArch64 fragment is the exception: verbatim from upstream `sail-arm`

The trust gap is being closed incrementally: `conformance.v` proves the walk
agrees with a transcription of the upstream `pt_walk`; `upstream_gen_bridge.v`
proves the mechanically-generated upstream predicates agree with the transcribed
ones; `upstream_ptw_bridge.v` proves the full walk structure matches. But a full
upstream derivation remains future work.

### What this means for kernel verification

The theorems about the machine are **sound reasoning about this model**. If the
kernel's invariants are expressed in terms of this model's types and proved to
be maintained by the kernel's code, then:

1. **The kernel's logic is machine-checked** (via whatever prover the kernel
   verification uses — Lean for Layer A, Rocq/Iris for Layer I concurrent)
2. **The hardware's guarantees are machine-checked** (via Tessera's Rocq proofs)
3. **The remaining gap** is that this model is not yet mechanically linked to
   upstream Sail ISA models — it's a hand-written specification that has been
   conformance-tested but not fully derived

The goal of the trust-line workstream is to close that gap: derive the Tessera
walk mechanically from upstream `sail-riscv`/`sail-arm`, so the chain is
**upstream ISA spec → generated Rocq → Tessera's proofs → kernel's invariants**.

## 7. Build and verification

```bash
cd hardware/rocq && bash build.sh
```

This:
1. Generates Rocq types from all Sail sources (`sail --rocq`)
2. Compiles all 53+ proof files
3. Verifies axiom hygiene on every module (646+ non-weak + 76+ weak checks)

The full build passes, all axioms-free.

## 8. Related documents

- `system-state-goals.md` — the 9 SSG goals (what state the kernel must keep consistent)
- `rigor-trust-line.md` — rigour/trust-boundary register (what's proved vs. trusted)
- `hardware-model-plan.md` — the modeling plan and backlog
- `stage2-shootdown.md` — the Stage 2 shootdown proof design
- `iommu-shootdown-plan.md` — the Stage 4 IOMMU proof design
- `formalization-status.md` — the full verification status (Lean + Rocq + Iris)
- `riscv-custom-mmu-extension.md` — the custom inverted page table extension
- `partner-hashing-inverted-pt.md` — the partner-hashing design
- `ssg9-grouping-hierarchy.md` — the SSG-9 topology hierarchy

## 9. Next steps for kernel verification (Stage 3)

With the machine model documented, the kernel verification (Stage 3) can proceed:

1. **Express kernel invariants** in terms of `Machine` types — TLB ⊆ page table,
   IOTLB ⊆ page table, refcount discipline, KAU integrity
2. **Prove kernel operations preserve invariants** — map, unmap, fork, COW-break,
   mprotect, swap (the Layer-A Lean proofs already exist; they need to be
   connected to this hardware model)
3. **Prove the shootdown protocol** (the kernel's IPI-based broadcast) refines the
   hardware model's shootdown theorems
4. **Cross-prover refinement** (Lean ↔ Rocq): connect the Layer-A algorithmic
   proofs to the Layer-I hardware model

The SSG-1 topology theorems (SMT co-residency, NUMA locality) are the first
consumers of the `hart`/`node` fields. The SSG-9 grouping hierarchy
(multikernel domains → framekernel → SSI → NORMA) is the long-range target
that uses the domain boundary to scale the verification.
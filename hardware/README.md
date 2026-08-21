# Tessera — hardware-state model (Sail → Rocq/Iris) + the end-to-end pass

Opens the kickoff §5 trust line: an executable, checked Sail model of the machine
state a clustered VMM runs on, connected to the Iris proofs in ../property2/coq.
See ../doc/hardware-model-plan.md (design) and ../doc/end-to-end-proving-pass.md
(the single-prover spine).

## Status (updated 2026-08-21)

### CPU MMU/TLB and shootdown — complete

- **H1** — `src/machine.sail`: functional machine skeleton + RISC-V Sv39 3-level
  walk + per-core TLB + SFENCE.VMA. Typechecks, generates Rocq, compiles.
- **Stage 1 (sequential §4 crux, root removal)** — `rocq/coherence.v`:
  `unmap_correct` + `unmap_without_flush_breaks_coherence` — axiom-free.
- **Stage 1.1 (sequential §4 crux, leaf removal)** — `rocq/coherence_leaf.v`:
  `unmap_leaf_correct` + `unmap_leaf_without_flush_breaks_coherence` — axiom-free.
- **Stage 2 (N-core broadcast shootdown)** — all stages landed:
  - **S2.0** — `rocq/shootdown.v`: `shootdown_correct` (pure sequential) — axiom-free.
  - **S2.1** — `rocq/shootdown_iris.v`: concurrent Iris HeapLang broadcast with
    ghost `gset` invariant — `wait_spec`, `remote_spec`, `broadcast_spec` — axiom-free.
  - **S2.2** — `rocq/shootdown_weak.v` → `shootdown_weak_broadcast.v`: the N-core
    weak-memory (gpfsl/ORC11) broadcast over the *concrete* generated machine —
    `shootdown_weak_gen_inv`, `bc_broadcast_spec` — axiom-free.
  - **S2.3** — `rocq/ipi.v`: IPI mailbox + `deliver_ipi`/`receive_ipi` transitions,
    `ipi_broadcast_correct` — axiom-free.
  - **S2.4** — `rocq/shootdown_weak_broadcast.v`: the weak-memory broadcast carries
    the IPI mailbox, ghost step = `receive_ipi (deliver_ipi _ i)` — axiom-free.
  - **S2.5** — `rocq/intc_weak_broadcast.v` / `shootdown_weak_broadcast_intc.v`:
    the interrupt controller (`intc.sail`) in the loop — send+ack produces the
    IPI mailbox, the remote's flush is gated on the controller's doorbell,
    masking/interrupt-context/priority modeled — axiom-free.

### Multi-architecture — complete (four variants)

Three additional MMU variants behind the same walk/refill/flush/lookup interface:
- **MIPS** software-refill (+ 1 KiB PageGrain, VPN2X) — `mips_tlb.sail` / `mips_tlb.v`.
- **LoongArch** software-refill (odd/even pair) — `loongarch_tlb.sail` / `loongarch_tlb.v`.
- **AArch64** VMSAv8-64 (block descriptors + contpte + LPA2) — `aarch64_tlb.sail` /
  `aarch64_tlb.v` (cross-checked against `sail-arm` `v8_base.sail` + Arm ARM DDI 0487).
Each with refill-handler/coherence/shootdown twins proved axiom-free.
RISC-V Svnapot (64KiB NAPOT pages, TLB superpage matching) also landed.

### IOMMU / DMA translation safety (SSG-4) — complete

- **S4.1** — IOTLB coherence (`IOTLB ⊆ mapping`), unmap-correct, fault-on-no-invalidate.
- **S4.2** — concurrent IOTLB shootdown, queued-invalidation command queue,
  Invalidation-Wait ordering, ATS device-TLB tier, weak-memory gpfsl lift.
- **S4.3** — ATS translation request/completion, PRI page-request, device-TLB
  invalidation, full ATS shootdown lift.
- **S4.5** — VT-d context/PASID/scalable-device-table, PASID-cache coherence/
  eviction/refill, generation tags, FRCD fault recording + drain, interrupt
  delivery of PRI faults, SMMUv3 two-stage walk, AMD-Vi 4-level walk, P_IOTLB
  pairing, granularity validity, weak-memory ghost lifts for all translation
  loops (SMMU/AMD-Vi/VT-d PASID, ATS, PRI), full ATS shootdown composition.

Cross-checked against VT-d 5.20, SMMUv3 H.a, AMD-Vi 3.11, and PCIe 6.0.

### Conformance — leaf-level

`rocq/conformance.v`: `translate_conforms` — exact agreement with a transcription
of the upstream `sail-riscv` `pt_walk`, no precondition, 7 executable vectors.
Remaining: full walk-level derivation from upstream Sail (see `rigor-trust-line.md` G1).

### Build

53 Rocq files; 646 non-weak + 76 weak axiom-free checks (722 total), all "Closed
under the global context", enforced by `build.sh` on every build.

## Layout

    src/machine.sail           machine skeleton + Sv39 walk + TLB + SFENCE.VMA + IOMMU + ATS/PRI
    src/intc.sail              interrupt controller (GIC-SGI / RISC-V AIA subset)
    src/mips_tlb.sail          MIPS software-refill TLB (+ 1 KiB PageGrain)
    src/loongarch_tlb.sail     LoongArch software-refill TLB
    src/aarch64_tlb.sail       AArch64 VMSAv8-64 (block + contpte + LPA2)
    src/sail_arm_tlb.sail      AArch64 fragment from sail-arm (ContiguousSize etc.)
    rocq/                      generated Rocq (machine.v, machine_types.v, intc.v, …)
    rocq/coherence.v           root-removal theorems (Stage 1)
    rocq/coherence_leaf.v      leaf-removal theorems (Stage 1.1)
    rocq/shootdown.v            N-core broadcast shootdown (S2.0)
    rocq/shootdown_iris.v      concurrent Iris HeapLang broadcast (S2.1)
    rocq/shootdown_weak.v      weak-memory (gpfsl) shootdown (S2.2a–c)
    rocq/shootdown_weak_broadcast.v  N-core weak-memory broadcast + IPI (S2.2c/S2.4)
    rocq/shootdown_weak_broadcast_intc.v  controller-in-the-loop (S2.5)
    rocq/ipi.v                 IPI delivery/receive transitions (S2.3)
    rocq/intc.v / intc_proofs.v / intc_priority.v  interrupt controller (SSG-3)
    rocq/data_ram.v            byte-addressable RAM + address decode
    rocq/conformance.v         leaf-level conformance vs upstream sail-riscv
    rocq/iommu_proofs.v        IOMMU coherence + shootdown (S4.1/S4.2)
    rocq/iommu_conformance.v  IOMMU conformance vectors
    rocq/iommu_broadcast_weak.v  weak-memory IOMMU broadcast (S4.2b-2)
    rocq/cmdq_mmio.v          command-queue MMIO (S4.2c)
    rocq/vtd_proofs.v          VT-d context/PASID/scalable/FRCD/PRI (S4.5)
    rocq/smmu_proofs.v         SMMUv3 two-stage walk (S4.4)
    rocq/amdvi_proofs.v        AMD-Vi 4-level walk (S4.4)
    rocq/pasid_translate_weak.v   weak PASID translation lift (S4.5)
    rocq/smmu_translate_weak.v    weak SMMU translation lift (S4.5)
    rocq/amdvi_translate_weak.v   weak AMD-Vi translation lift (S4.5)
    rocq/ats_devtlb_weak.v     weak ATS device-TLB lift (S4.3/S4.5)
    rocq/pri_fault_weak.v      weak PRI fault delivery lift (S4.5)
    rocq/pri_fault_intc_weak.v weak PRI → INTC delivery + drain (S4.5)
    rocq/build.sh              Sail -> Rocq -> checked .vo (single command)

## Toolchain

- Sail 0.20.2 (opam switch `rocq-9.2`), Rocq backend `--rocq` (SailStdpp style).
- Support library: `rocq-sail-stdpp` 0.20.2 (opam), plus `rocq-stdpp-bitvector`,
  `rocq-stdlib`, `rocq-stdpp`, `rocq-iris` 4.5.0.
- gpfsl vendored into `third_party/gpfsl` (built by `third_party/build.sh` on the
  same rocq-9.2 switch — no separate `wm` switch).

## Build

    hardware/rocq/build.sh     # typecheck + generate + compile + axiom-check (all in one)

## Mapping to the existing proof

- The concrete `unmap_correct` / `unmap_without_flush_breaks_coherence` here are
  the hardware-level twins of the abstract `Tlb.lean` theorems (proof/Tessera),
  now with the walk generated rather than trusted.
- The Iris shootdown (`shootdown_iris.v`) is Stage 2: the concurrent protocol
  over this concrete multi-core machine; the weak-memory lift (`shootdown_weak*.v`)
  is Property 2 (gpfsl/ORC11).
- The IOMMU track (`iommu_*.v` / `vtd_proofs.v` / `smmu_proofs.v` / `amdvi_proofs.v`)
  is the CPU-TLB coherence problem replayed at the device translation point.

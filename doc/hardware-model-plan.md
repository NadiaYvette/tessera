# Tessera — hardware-state modeling plan (Sail → Coq/Iris)

Status: H1 landed (2026-08-13) — the Sail machine skeleton + RISC-V Sv39 walk + TLB + SFENCE.VMA typechecks and generates Rocq that compiles (hardware/rocq, see build.sh).
This opens the kickoff §5 trust line: replace the trusted "the MMU walks page
tables thus" with an executable, checked Sail model of the translation/cluster
state, connected to the Iris track (property2/coq).

## Goal

Model, from the hardware up, the state a clustered VMM runs on: physical memory,
page-table descriptors, the translation walk, per-core TLBs, caches, and multiple
cores/clusters. End state: Layer-I (real PTEs, walks, TLBI) is reasoned against a
real ISA model rather than a trusted assumption, and clusters are modeled
end-to-end.

## Decisions (2026-08-13 session)

- Multi-architecture is first-class: a parameterized machine skeleton + a pluggable
translation/MMU-variant interface. RISC-V first; hardware-walker (AArch64) and
software-refill (mips) next; any new Sail ISA model drops in behind the interface.
- Backend: Sail → Coq (the Rocq target, sail_coq_backend), feeding Iris (property2/coq).
- Scope: SMP/cluster from the start (multi-core, per-core TLB, shootdown) at the
translation level — per arch-coverage.md, the VM/TLB layer is what matters.

## Toolchain (verified in this environment)

- Sail 0.20.2 (opam switch rocq-9.2), all backends: coq/rocq, lean, lem, ocaml, c,
  smt, sv, latex, doc.
- libsail 0.20.2 ships lib/prelude.sail and lib/concurrency_interface (SMP support),
  plus a vendored AArch64 model (aarch64/ full + duopod, with translation/TLB and
  aarch64_extras.v/_CoqProject for Coq generation) and aarch64_small/.
- rocq-iris 4.5.0 + rocq-iris-heap-lang in the same switch.
- Rocq backend is `--rocq` (emits SailStdpp-style code); the older `--coq` backend emits
  the legacy Sail2/bbv library (vendored only as `snapshots/coq/lib/coq/Sail2_*.v`).
- Support library: `rocq-sail-stdpp` 0.20.2 (`opam install rocq-sail-stdpp`) provides
  SailStdpp.{Base,Real,...} and pulls `rocq-stdpp-bitvector`. It is NOT shipped with
  the `sail`/`sail_coq_backend` packages and must be installed explicitly.
- Invocation (verified): `sail --just-check src/machine.sail`, then
  `sail src/machine.sail --rocq --rocq-output-dir rocq -o machine`, then
  `rocq compile -Q <uc>/stdpp stdpp -Q <uc>/SailStdpp SailStdpp -Q <uc>/iris iris
   rocq/machine_types.v rocq/machine.v` — see `hardware/rocq/build.sh`.
- Local ISAs already cloned for later variants: ~/src/sail-riscv, ~/src/sail-arm,
  ~/src/sail-cheri-mips, ~/src/sail-x86-from-acl2; ~/src/sail/snapshots/coq/riscv/ has a
  full RISC-V model already generated to (legacy Sail2) Coq.

## Machine skeleton (architecture-agnostic)

- N cores; each: a register file and an explicit TLB (set of (VA → PA, perm)).
- Shared physical memory; page tables resident in physical memory.
- Translation interface: translate : VA → Option (PA, perm); invalidate : Range →
  Unit; shootdown (IPI + broadcast invalidate). Modeled explicitly so a missing
  flush is a provable error (kickoff §4, the crux).

## MMU-variant interface (the pluggability point)

Three regimes (mmu-variants.md):
1. hardware page-table walker (x86-64, AArch64, RISC-V) — walk is hardware, modeled.
2. software-refill TLB (mips, sparc) — refill handler is our code; a theorem, not an
   assumption.
3. inverted/hashed page tables (PPC pre-Radix, PA-RISC) — changes Layer I, not the
   invariants.

Each variant supplies walk/refill semantics behind the same interface, so the
skeleton and the Iris proofs are variant-parameterized (mirrors arch-coverage.md's
"the protocol reasoning is architecture-agnostic").

## Milestones (each standalone, per kickoff §1)

- H1 ✅ — type-checked Sail model of the skeleton + RISC-V Sv39 walk + TLB + SFENCE.VMA,
  generating Rocq that compiles. DONE 2026-08-13: hardware/src/machine.sail + hardware/rocq/build.sh.
- H2 — connect generated Rocq to the kernel-control theorems. ✅ **Stages 1 + 1.1 done**
  (2026-08-13): `hardware/rocq/coherence.v` proves `unmap_correct` and
  `unmap_without_flush_breaks_coherence` (root removal), and
  `hardware/rocq/coherence_leaf.v` proves `unmap_leaf_correct` and
  `unmap_leaf_without_flush_breaks_coherence` (leaf removal) over the generated Sv39
  walk (all axiom-free). Remaining: the concurrent Iris shootdown over the concrete
  machine (Stage 2).
- H3 — SMP shootdown: multi-core Sail + the P2.4 weak-memory protocol instantiated on
  the generated model.
- H4 — second MMU variant (AArch64 from the vendored model, or software-refill mips)
  behind the same interface; prove the skeleton proofs are variant-parameterized.
- H5 — isla/islaris for symbolic execution / verified page-table-manipulation assembly.

## Open questions / next

- RISC-V Sail source: write a focused translation-only model first (the full ISA is
  not needed to reason about the MMU/TLB/shootdown); vendor the open riscv-sail model
  later for assembly-level (Islaris-style) verification.
- Naming: hardware/ (Sail sources + generated coq/ + emulator/) parallel to proof/
  (Lean), property2/ (Coq+Iris), rust/ (Kani).

## Backlog (long-range, not sequenced — revisit after S2.1/S2.2)

Remembered so they are not lost; each lists its conformance oracle / fidelity risk.

- **RISC-V Svnapot** — ✅ **walk done** (2026-08-16): the `N` bit (`Pte.napot`),
  `napot_guard` (ppn[3..0] = 0b1000) and `napot_phys_addr` (ppn[43..4] @ VA[15..0],
  the 64KiB low-PPN-substitution) are in `machine.sail`'s `translate` at the level-0
  leaf, and N=1 on a *non-leaf* pointer PTE is reserved ⇒ fault (upstream
  `pte_is_invalid`'s "non-leaf ∧ ext bits ≠ 0" clause, mirrored in `leaf_addr` +
  the coherence_leaf.v proofs). `translate_conforms` still holds axiom-free and
  six executable vectors (`test_vector_napot_*`) pin the decode, the reserved
  encodings, and oracle agreement. Transcribed from sail-riscv
  `model/sys/vmem.sail` ll. 190-196 + `vmem_pte.sail` PTE_Ext.N. **Remaining**
  (one follow-up): TLB superpage matching — a 64KiB entry tags on VA[38..16], so
  `find_tlb`/`tlb_lookup`/`sfence_vma_va` need page-size-aware matching (the
  per-cell coupling already threads `vaddr`; this adds a `napot`/granularity
  field to `TlbEntry`).
- **MIPS PageGrain (1 KiB, ESP) + software-refill** — the `mmu-variants.md`
  demonstration platform. Hand-write a translation-only Sail model (TLB + CP0
  `PageGrain`/`PageMask`/`EntryHi`/`EntryLo` + `compute_pagemask`). **A conformance
  oracle already exists**: `~/src/QEMU` branch `nadia.chambers/page-grain-001`
  (4 commits, MD00091-cited). Key semantics it encodes: enable = `Config3.SP ∧
  PageGrain.ESP`; PageMask is a run of 1s with even count (the `{4^k·M}` spectrum);
  `pfn_shift = 10` (vs 12) under ESP; `VPN2X = EntryHi[12:11]`; MaskX stored "as
  if 0b11" when ESP=0. Differential-test the Sail model against it (closes G1).
- **LoongArch** — next arch of interest (telix target: `kernel/src/arch/loongarch64/`,
  QEMU runner present). Software-refill (MIPS-like) → reuse the refill-handler
  theorem; but **no upstream Sail model exists**, so hand-write from the manual and
  differential-test against QEMU's loongarch64 TCG (the only oracle).
- **Toolchain reconciliation (S2.2)** — gpfsl onto rocq-9.2 (dev iris) or the machine
  onto coq 8.20; see `rigor-trust-line.md` §6.
- **Compiler-verification / trust-boundary relocation (far future)** — the
  Singularity/Midori direction (`~/src/frankenstein`, `~/src/organ-bank`) moves the
  security boundary from the unverifiable MMU to the verifiable compiler/runtime;
  K-specs (`organ-ir.k`, `perceus-claims.k`) are the seed. See `rigor-trust-line.md`.

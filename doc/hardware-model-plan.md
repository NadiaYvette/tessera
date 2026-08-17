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
  `model/sys/vmem.sail` ll. 190-196 + `vmem_pte.sail` PTE_Ext.N. **TLB superpage
  matching done** (2026-08-16): `TlbEntry` gains a `napot` flag, `tag_eq`
  matches a 64KiB entry on VA[38..16] (dropping the low 4 VPN bits), `tlb_pa`
  composes the 16-bit-offset PA (ppn[43..4] @ VA[15..0]), and
  `find_tlb`/`tlb_lookup`/`sfence_vma_va` are page-size-aware. `find_tlb_napot_leaf`
  + two vectors pin the 64KiB-page coverage and the flush. All coherence/shootdown
  lemmas stay axiom-free.
- **MIPS PageGrain (1 KiB, ESP) + software-refill** — the `mmu-variants.md`
  demonstration platform. **Done** (2026-08-16): the Sail transcription is
  `hardware/src/mips_tlb.sail` (ESP/VPN2X/1 KiB-capable), generated into
  `hardware/rocq/mips_tlb.v`/`mips_tlb_types.v`; the proofs over the generated
  model are `hardware/rocq/mips_tlb_proofs.v`; the QEMU differential oracle is
  `hardware/rocq/mips_qemu_oracle.v`. `compute_mask_level` (the PageMask
  run-of-1s/even-count decode, `{4^k·M}` spectrum), `MipsEntry`/`mips_lookup`/
  `mips_pa` (page-size-aware match `vpn[27..level] == va[39..12+level]` and
  translation `pfn @ va[11+level..0]`), `mips_refill` (the software refill
  handler), and `mips_vpn2x` (`EntryHi[12:11]`, the 1 KiB VPN2X field) are all
  now *generated from Sail*, not hand-written. The trust-boundary win is
  `mips_refill_lookup_covers`: refill-then-lookup is the entry's translation
  when the entry covers the address — a *theorem about our refill handler*, not
  a trusted hardware walker. The even-run characterization
  (`compute_mask_level_unfold`/`compute_mask_level_some_even`) plus 27
  axiom-free vectors pin spectrum acceptance/rejection (incl. `esp` 1 KiB),
  base/page shift (`mips_page_shift true 0 = 10` vs `false 0 = 12`), the four
  `VPN2X` encodings, page-size-aware match, and PA translation. **QEMU oracle
  diff-test**: `compute_mask_level_conforms` proves the Sail decode equals a
  faithful transcription of QEMU's `compute_pagemask` (`~/src/QEMU` branch
  `nadia.chambers/page-grain-001`, MD00091-cited), bridged by `qemu_cto_cto18`;
  16 executable diff vectors cover decode agreement (lvl0/2/4, odd, non-run,
  esp-lvl2), PA translation (1k/4k/16k/esp-4k) and page-size-aware match.
  Key semantics encoded: enable = `Config3.SP ∧ PageGrain.ESP`; PageMask is a
  run of 1s with even count (the `{4^k·M}` spectrum); `pfn_shift = 10` (vs 12)
  under ESP; `VPN2X = EntryHi[12:11]`; MaskX stored "as if 0b11" when ESP=0.
  See `mips-software-refill.md` (closes G1). **Shootdown integration done**
  (2026-08-17): `mips_flush` (software TLB invalidate) added to the Sail model;
  the MIPS twins of the coherence/shootdown theorems are proved axiom-free in
  `mips_tlb_proofs.v` — `mips_flush_clears`, `mips_unmap_without_flush_breaks_coherence`,
  `mips_refill_flush_composes`, and `mips_shootdown_correct`. **Live QEMU diff-test
  done** (2026-08-17): `hardware/qemu-diff/run_mips_decode_diff.sh` extracts
  `compute_pagemask` verbatim from `~/src/QEMU` and runs the six decode vectors,
  confirming real QEMU code agrees with the model; wired into `ci.sh` (skipped
  when QEMU/`cc` absent).
- **LoongArch** — telix target: `kernel/src/arch/loongarch64/`, QEMU runner
  present. Software-refill (MIPS-like) → reuse the refill-handler theorem; **no
  upstream Sail model exists**, so hand-written from QEMU's loongarch64 TCG (the
  only oracle). **Core done** (2026-08-17): `hardware/src/loongarch_tlb.sail`
  (generated into `loongarch_tlb.v`/`loongarch_tlb_types.v`) models the two
  LoongArch-specific features — the per-entry `ps` page shift (not MIPS's
  PageMask decode) and the **odd/even pair** (an entry covers two adjacent pages
  of size `2^ps`; VPPN = VA[47:13]; `pa = pfn[35:ps-12] @ va[ps-1:0]` with
  `va[ps]` selecting pfn0/pfn1). `loongarch_tlb_proofs.v` proves
  `la_refill_lookup_covers` (the refill-handler trust-boundary win) and the
  coherence/shootdown twins (`la_flush_clears`,
  `la_unmap_without_flush_breaks_coherence`, `la_refill_flush_composes`,
  `la_shootdown_correct`), plus 14 `vm_compute` vectors (4 KiB/16 KiB
  odd/even match, PA translation, refill/flush). **QEMU oracle diff-test
  done** (2026-08-17): `loongarch_qemu_oracle.v` transcribes
  `loongarch_tlb_search_cb`/`loongarch_map_tlb_entry`/`loongarch_check_pte`
  with *different* expressions and pins match/PA agreement via 11 executable
  diff vectors. **Live QEMU diff-test done** (2026-08-17):
  `hardware/qemu-diff/run_loongarch_diff.sh` extracts `check_ps` verbatim and
  runs an independent C transcription of the match/PA on the same vectors;
  wired into `ci.sh`. See `loongarch-software-refill.md`.
- **Toolchain reconciliation (S2.2)** — gpfsl onto rocq-9.2 (dev iris) or the machine
  onto coq 8.20; see `rigor-trust-line.md` §6.
- **Compiler-verification / trust-boundary relocation (far future)** — the
  Singularity/Midori direction (`~/src/frankenstein`, `~/src/organ-bank`) moves the
  security boundary from the unverifiable MMU to the verifiable compiler/runtime;
  K-specs (`organ-ir.k`, `perceus-claims.k`) are the seed. See `rigor-trust-line.md`.

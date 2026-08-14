# Tessera — the end-to-end proving pass

**Goal.** One pipeline that *sets up a model of the hardware for the kernel to
control*, then *proves the kernel's control of it correct* — from concrete
(generated) machine state, through the kernel's MMU/TLB operations, to the
coherence theorem, all checked by one prover in one command.

## Why the existing pieces do not yet compose

Tessera is a multi-prover, multi-fidelity tower, each rung a standalone result
(kickoff §1) connected to the next only by intent, not by refinement:

- **Lean (S/A/I):** the TLB is an abstract `List TlbEntry`; *the walk is trusted*
  (kickoff §5). `Tlb.lean` proves `unmap_correct` / `unmap_without_flush_breaks_coherence`
  against the abstract mapping `Nat → Prop`.
- **Coq + Iris (Property 2):** the TLB and PTE are HeapLang *booleans*
  (`tlb_shootdown.v`); the walk is abstracted away entirely.
- **Sail → Rocq (hardware, H1):** the *real* Sv39 walk, per-core TLB, and
  SFENCE.VMA are modeled and generated (`hardware/rocq/machine.v`) — but with no
  theorem about the kernel controlling them.

Cross-prover refinement (Lean ↔ Coq ↔ Sail) has no shared semantic domain, so the
end-to-end pass must be a **single refinement spine in a single prover**. Rocq is
the only prover where the concrete generated model, the TLB-as-state, *and* Iris
(for the later concurrent stage) all coexist.

## The spine

    concrete hardware (generated Sail → Rocq, hardware/rocq/machine.v)
          │  translate : Core → list MemEntry → mword 64 → option (mword 56 × Perm)
          │  tlb_lookup : Core → mword 64 → option (mword 56 × Perm)
          │  sfence_vma_all / sfence_vma_va : Core → Core
          ▼
    kernel control (hand-written Rocq over the generated types, coherence.v)
          │  remove_entry : list MemEntry → mword 56 → list MemEntry   (* the PTE write *)
          │  unmap        : Core → mem → va → (Core × mem)             (* PTE write + SFENCE *)
          │  unmap_without_flush                                          (* PTE write only  *)
          ▼
    coherence theorem (§4 crux, now with the hardware, not trusted pseudocode)
          unmap_correct                      : walk = None  ∧  tlb = None
          unmap_without_flush_breaks_coherence : walk = None  ∧  tlb = Some (pa, perm)

## The joint (Stage 1 — sequential §4 crux)

The generated `machine.v` already exposes exactly the right surface, as pure
(non-monadic) definitions: `translate`, `tlb_lookup`, `sfence_vma_all`,
`sfence_vma_va`, `read_pte` (a `Fixpoint` over `eq_vec`). Stage 1 adds the kernel
control operations and the two coherence theorems **without changing the Sail
source** — the hardware stays generated; only the control layer and proofs are
hand-written Rocq.

**Concrete coherence.** The mapping is the walk: `fun va ⇒ translate core mem va`.
The TLB cache is `core.tlb`; a cached translation is `tlb_lookup core va`. Coherence
is agreement between them. An `unmap` that removes the PTE for a translation but
omits the flush leaves `translate = None` while `tlb_lookup = Some (pa, perm)` — the
stale-entry use-after-free, now a *provable* error over the real walk.

**Why the proof is tractable.** The walk faults at level 2 when the root PTE entry
is absent, so `translate` reduces to `read_pte … = None` *before* any address
arithmetic is forced: `pte_address` / `phys_addr` stay opaque, and the proof needs
only (i) list induction and (ii) `SailStdpp.Operators_mwords.eq_vec_true_iff`
(`eq_vec v w = true ↔ v = w`). This is the deliberate Stage-1 simplification
(kickoff §1: each milestone complete in itself). Stage 1.1 (leaf removal) needs no
more: the intermediate levels survive by *decidability* of `eq_vec` — case analysis
on `eq_vec a addr` (`eq_vec_false_iff` when it differs) — so `pte_address` is still
never reduced.

## Lemmas and theorems (Stage 1)

1. `eq_vec_refl a : eq_vec a a = true` — from `eq_vec_true_iff`.
2. `read_pte_absent_after_remove mem a : read_pte (remove_entry mem a) a = None`
   — induction on `mem`; the removed branch reuses IH, the kept branch rewrites
   `eq_vec e.addr a = false`.
3. `find_tlb_absent_after_filter entries vpn off : find_tlb (filter_tlb entries vpn) vpn off = None`
   — the SFENCE.VMA-by-VA analogue (TLB entry for the flushed VA is gone).
4. `unmap_faults core mem va : translate core (remove_entry mem (pte_address satp_ppn (vpn2 va))) va = None`
   — the PTE write alone invalidates the translation (walk misses at level 2).
5. `tlb_stale core va e : core.tlb = [e] → e.vpn = vpn_of va → tlb_lookup core va = Some (phys_addr e.ppn (page_offset va), e.perm)`
   — a cached entry still answers, even though the walk now faults.
6. **`unmap_correct`** — remove + `sfence_vma_va`: `translate = None ∧ tlb_lookup = None`.
7. **`unmap_without_flush_breaks_coherence`** — remove only: `translate = None ∧
   ∃ pa perm, tlb_lookup = Some (pa, perm)`. The forgotten flush is a provable error.

## Lemmas and theorems (Stage 1.1)

8. `read_pte_remove_other mem a b : a ≠ b → read_pte (remove_entry mem a) b = read_pte mem b`
   — removing the leaf entry leaves every other address untouched (list induction;
   the removed branch uses `eq_vec_false_iff`).
9. `leaf_addr core mem va` — the kernel's software walk (mirror of `translate`)
   that returns the *address* of the level-0 PTE instead of the translation.
10. `leaf_addr_none_implies_translate_none` — if the software walk faults, so does
    the hardware walk (they share the same `read_pte` calls on the same memory).
11. `leaf_addr_removal_faults core mem va a : leaf_addr core mem va = Some a →
    translate core (remove_entry mem a) va = None` — the PTE write at the leaf
    address alone invalidates the translation (case analysis on `eq_vec a` against
    the two intermediate addresses; the surviving levels rewrite via
    `read_pte_remove_other`, the removed level via `read_pte_absent_after_remove`).
12. **`unmap_leaf_correct`** — leaf PTE write + `sfence_vma_va`:
    `translate = None ∧ tlb_lookup = None`.
13. **`unmap_leaf_without_flush_breaks_coherence`** — leaf PTE write only:
    `translate = None ∧ ∃ pa perm, tlb_lookup = Some (pa, perm)`. The forgotten
    flush is again a provable error.

## Trust line (what this moves and what stays)

- **Now modeled and proved:** the page-table walk (generated Sv39), the TLB as
  explicit cache, and that the kernel's unmap+flush re-establishes coherence while
  a flush-less unmap provably breaks it. The kickoff §5 line "the MMU walks page
  tables thus" is no longer *assumed* for the fault-on-absent-entry behavior — it is
  the generated code.
- **Still trusted:** that the generated `mword`/bitvector substrate
  (`SailStdpp`) faithfully models machine words, and that the association-list
  memory (`list MemEntry`) is an adequate model of physical memory (address
  decoding, bus, caches). A real bit-level memory model is a later increment.
- **Still deferred:** Property 2 (concurrent shootdown ordering) — Stage 2, over
  Iris, on this same concrete machine.

## Milestones

- **Stage 1** ✅ **DONE (2026-08-13)** — sequential §4 crux over the concrete walk.
  `hardware/rocq/coherence.v` proves `unmap_correct` and
  `unmap_without_flush_breaks_coherence` over the generated Sv39 walk; both are
  **closed under the global context** (axiom-free). Built by `hardware/rocq/build.sh`.
- **Stage 1.1** ✅ **DONE (2026-08-13)** — leaf-entry (data-dependent) removal:
  `hardware/rocq/coherence_leaf.v` generalizes theorem 4/6/7 from root-removal to
  leaf-removal: `unmap_leaf` software-walks to the level-0 PTE, removes it, and
  flushes; `unmap_leaf_correct` and `unmap_leaf_without_flush_breaks_coherence` are
  both **closed under the global context** (axiom-free). The intermediate levels
  survive by `eq_vec` decidability (`read_pte_remove_other`), so — contrary to the
  original estimate — no `pte_address` bitvector inequalities were needed.
- **Stage 2** 🔶 — the N-core broadcast shootdown over the concrete multi-core
  `Machine` (see `doc/stage2-shootdown.md`). **S2.0 done (2026-08-13)**:
  `hardware/rocq/shootdown.v` proves `shootdown_correct` — after removing the leaf
  PTE and `sfence_vma_va`-ing every core, *no core* translates the freed frame
  (`translate = None ∧ tlb_lookup = None`), axiom-free. Remaining: **S2.1** the
  concurrent Iris HeapLang proof (broadcast-barrier invariant, concrete heap
  values), then **S2.2** the gpfsl weak-memory lift.
- **Stage 3** — ABI refinement over the walk: `translate` computes exactly the
  abstract Layer-S mapping (`tilingMapping` in `proof/Tessera/RefinementS.lean`),
  the cross-prover joint documented as a statement, not a mechanical link.

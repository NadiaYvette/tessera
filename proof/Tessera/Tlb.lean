/-
  Tessera — Layer A / M2 (flagship): the TLB-coherence obligation for `unmap`.

  See ../doc/tessera-verification-kickoff.md §4 — the crux of the brief, and its
  "single most important instruction": *model the TLB as explicit state and make a
  missing flush a provable error.*

  We model the **abstract mapping** (which virtual granules are currently mapped)
  and the **TLB** (a set of cached virtual ranges) as separate state, state the
  coherence invariant `TLB ⊆ mapping` (invariant 7, presence form: no cached entry
  for an unmapped granule — exactly the stale-entry / use-after-free obligation),
  and prove:

    * `unmap_correct` — `unmap r`, *with* its flush, leaves `r` unmapped, leaves no
      TLB entry covering `r`, and preserves coherence;
    * `unmap_without_flush_breaks_coherence` — `unmap r` that updates the mapping
      but *omits* the flush does **not** preserve coherence. The forgotten flush is
      a provable error, precisely as §4 demands.

  This is the sequential Property-1 obligation. The concurrent shootdown (how other
  cores come to observe the invalidation, Property 2) is deferred (§5, §6).

  Empirically this is the #1 / flagship failure mode in both telix and pgcl history
  (stale TLB after unmap/protection-change → use-after-free / stale read); see
  ../doc/failure-modes-telix.md (#9,#10) and ../doc/failure-modes-pgcl.md (#10,#12).
-/
import Tessera.Basic

namespace Tessera

/-- The **abstract mapping**: the set of currently-mapped virtual granules. This is
the Layer-S view; the extent set of `Basic.lean` refines it (that connection is
M3). -/
abbrev Mapping := Nat → Prop

/-- A **TLB entry**: a cached translation for the virtual granule range
`[vbase, vbase + vsize)`. `vsize > 1` models a superpage entry. We track presence
coherence (no cached entry for an unmapped granule), which is the stale-entry /
use-after-free obligation that `unmap` must discharge. -/
structure TlbEntry where
  vbase : Nat
  vsize : Nat
deriving DecidableEq, Repr

/-- The granules a TLB entry caches. -/
def TlbEntry.covers (t : TlbEntry) (v : Nat) : Prop := t.vbase ≤ v ∧ v < t.vbase + t.vsize

/-- **Invariant 7 (TLB coherence), presence form**: every granule cached by any TLB
entry is currently mapped — `TLB ⊆ mapping`. No cached translation survives for an
address that is not mapped. -/
def TlbCoherent (m : Mapping) (tlb : List TlbEntry) : Prop :=
  ∀ t ∈ tlb, ∀ v, t.covers v → m v

/-- The virtual range `[rb, rb + rs)` an `unmap` targets (e.g. an extent
`e : Extent` corresponds to the range `⟨e.base, e.size⟩`). -/
structure Range where
  rb : Nat
  rs : Nat
deriving DecidableEq, Repr

/-- The granules a range covers. -/
def Range.covers (r : Range) (v : Nat) : Prop := r.rb ≤ v ∧ v < r.rb + r.rs

/-- A TLB entry **overlaps** a range when their granule intervals intersect — then
`unmap` must flush it. An `abbrev` so the `Decidable` instance (an `And` of `Nat`
comparisons) is found automatically and can drive the flush filter. -/
abbrev TlbEntry.Overlaps (t : TlbEntry) (r : Range) : Prop :=
  t.vbase < r.rb + r.rs ∧ r.rb < t.vbase + t.vsize

/-- Intervals that share a granule overlap. -/
theorem not_overlaps_not_covers {t : TlbEntry} {r : Range} (h : ¬ t.Overlaps r)
    {v : Nat} (htv : t.covers v) (hrv : r.covers v) : False := by
  simp only [TlbEntry.covers] at htv
  simp only [Range.covers] at hrv
  exact h ⟨by omega, by omega⟩

/-- `unmapMap m r`: remove range `r` from the abstract mapping (the mapping update
half of `unmap`). -/
def unmapMap (m : Mapping) (r : Range) : Mapping := fun v => m v ∧ ¬ r.covers v

/-- `flush tlb r`: invalidate every TLB entry overlapping `r` (the TLB-maintenance
half of `unmap` — the step a buggy `unmap` forgets). -/
def flush (tlb : List TlbEntry) (r : Range) : List TlbEntry :=
  tlb.filter (fun t => decide (¬ t.Overlaps r))

/-- A surviving (un-flushed) TLB entry was in the TLB and does not overlap `r`. -/
theorem mem_flush {t : TlbEntry} {tlb : List TlbEntry} {r : Range}
    (ht : t ∈ flush tlb r) : t ∈ tlb ∧ ¬ t.Overlaps r := by
  simp only [flush, List.mem_filter, decide_eq_true_eq] at ht
  exact ht

/-- After `unmap r`, no granule of `r` is mapped. -/
theorem unmap_removes (m : Mapping) (r : Range) :
    ∀ v, r.covers v → ¬ (unmapMap m r) v := by
  intro v hv hm
  exact hm.2 hv

/-- After `unmap r` *with its flush*, no surviving TLB entry covers any granule of
`r` — the stale-entry / use-after-free window is closed. -/
theorem flush_clears (tlb : List TlbEntry) (r : Range) :
    ∀ t ∈ flush tlb r, ∀ v, t.covers v → ¬ r.covers v := by
  intro t ht v htv hrv
  exact not_overlaps_not_covers (mem_flush ht).2 htv hrv

/-- **`unmap` preserves TLB coherence** (invariant 7): if the entry survived the
flush it does not overlap `r`, so the granule it caches is not in `r`; it was mapped
before and is still mapped after (only `r` was removed). -/
theorem unmap_coherent (m : Mapping) (tlb : List TlbEntry) (r : Range)
    (h : TlbCoherent m tlb) : TlbCoherent (unmapMap m r) (flush tlb r) := by
  intro t ht v htv
  obtain ⟨htmem, hnov⟩ := mem_flush ht
  show m v ∧ ¬ r.covers v
  refine ⟨h t htmem v htv, ?_⟩
  intro hrv
  exact not_overlaps_not_covers hnov htv hrv

/-- **M2 flagship — `unmap` is correct.** Mirrors the brief's §4 statement: after
`unmap r`, region `r` is absent from the abstract mapping, no TLB entry covers `r`,
and TLB coherence is re-established. An `unmap` whose definition lacked the `flush`
would fail the second and third conjuncts — see below. -/
theorem unmap_correct (m : Mapping) (tlb : List TlbEntry) (r : Range)
    (h : TlbCoherent m tlb) :
    (∀ v, r.covers v → ¬ (unmapMap m r) v) ∧
    (∀ t ∈ flush tlb r, ∀ v, t.covers v → ¬ r.covers v) ∧
    TlbCoherent (unmapMap m r) (flush tlb r) :=
  ⟨unmap_removes m r, flush_clears tlb r, unmap_coherent m tlb r h⟩

/-- **The forgotten flush is a provable error.** An `unmap` that updates the
abstract mapping but omits the TLB flush does *not* preserve coherence: there is a
coherent state in which, after removing the range from the mapping while leaving the
TLB untouched, a stale entry still caches the now-unmapped granule. This is the §4
use-after-free made visible — the whole point of putting the TLB in the model. -/
theorem unmap_without_flush_breaks_coherence :
    ∃ (m : Mapping) (tlb : List TlbEntry) (r : Range),
      TlbCoherent m tlb ∧ ¬ TlbCoherent (unmapMap m r) tlb := by
  refine ⟨(fun v => v = 0), [{ vbase := 0, vsize := 1 }], { rb := 0, rs := 1 }, ?_, ?_⟩
  · -- coherent before: the one cached granule (0) is mapped
    intro t ht v htv
    simp only [List.mem_singleton] at ht
    subst ht
    simp only [TlbEntry.covers] at htv
    show v = 0
    omega
  · -- not coherent after a flush-less unmap: entry ⟨0,1⟩ still caches granule 0,
    -- which is now unmapped
    intro hcoh
    obtain ⟨_, hnr⟩ := hcoh { vbase := 0, vsize := 1 } (by simp) 0
      (by simp only [TlbEntry.covers]; omega)
    exact hnr (by simp only [Range.covers]; omega)

end Tessera

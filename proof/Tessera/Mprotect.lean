/-
  Tessera — Layer A / M2: `mprotect` TLB coherence (the permission half of §4).

  `Tlb.lean` proved the *presence* half of the §4 obligation: after `unmap`, no TLB
  entry caches a translation for an unmapped granule. This file proves the
  *permission* half: after `mprotect` narrows (or changes) the rights on a range, no
  TLB entry may still cache the *old* permissions — the stale-write-permission bug
  (telix #9/#10: a write-protect whose stale writable TLB entry lets the write
  through).

  We model a permission-carrying mapping (`PMapping := Nat → Option Perm`) and a TLB
  whose entries cache the permissions they believe are in force. Coherence is **exact
  agreement**: every cached entry's perms equal the current mapping's perms over every
  granule it covers. This single invariant subsumes presence (an unmapped granule is
  `none`, which equals no `some`, so no entry may cover it) and forbids both stale
  presence and stale permissions; its security-critical content is that no entry ever
  grants a permission the mapping has revoked.

  Results mirror `Tlb.lean`: `mprotect_correct` (with its flush, the new perms take
  effect, the frame is preserved, and coherence is re-established) and
  `mprotect_without_flush_breaks_coherence` (the flush-less variant is a provable
  error). The "demote first if it's a superpage" obligation is category E and is
  parameterized out here.
-/
import Tessera.Basic

namespace Tessera

/-- A **permission-carrying mapping**: each virtual granule is unmapped (`none`) or
mapped with permissions (`some p`). -/
abbrev PMapping := Nat → Option Perm

/-- A TLB entry that caches, for a virtual range `[vbase, vbase+vsize)`, the
permissions `perms` it believes are in force. -/
structure PTlbEntry where
  vbase : Nat
  vsize : Nat
  perms : Perm
deriving DecidableEq, Repr

/-- The granules a TLB entry caches (`abbrev` so its `Decidable` instance is found). -/
abbrev PTlbEntry.covers (t : PTlbEntry) (v : Nat) : Prop := t.vbase ≤ v ∧ v < t.vbase + t.vsize

/-- The virtual range an `mprotect` targets. -/
structure PRange where
  rb : Nat
  rs : Nat
deriving DecidableEq, Repr

/-- The granules a range covers (`abbrev` so its `Decidable` instance is found). -/
abbrev PRange.covers (r : PRange) (v : Nat) : Prop := r.rb ≤ v ∧ v < r.rb + r.rs

/-- A TLB entry **overlaps** a range when their granule intervals intersect. -/
abbrev PTlbEntry.Overlaps (t : PTlbEntry) (r : PRange) : Prop :=
  t.vbase < r.rb + r.rs ∧ r.rb < t.vbase + t.vsize

/-- **Invariant 7 (TLB coherence), permission form**: every TLB entry's cached
permissions agree exactly with the current mapping over every granule it covers. No
cached translation contradicts the mapping — in particular none grants a revoked
permission. -/
def PTlbCoherent (m : PMapping) (tlb : List PTlbEntry) : Prop :=
  ∀ t ∈ tlb, ∀ v, t.covers v → m v = some t.perms

/-- `mprotect r np`: set the permissions of the *mapped* granules of `r` to `np`
(unmapped granules stay unmapped); leave everything outside `r` unchanged. -/
def mprotectMap (m : PMapping) (r : PRange) (np : Perm) : PMapping :=
  fun v => if r.covers v then (m v).map (fun _ => np) else m v

/-- `pflush tlb r`: invalidate every TLB entry overlapping `r` (the maintenance
`mprotect` must perform — the step a buggy `mprotect` forgets). -/
def pflush (tlb : List PTlbEntry) (r : PRange) : List PTlbEntry :=
  tlb.filter (fun t => decide (¬ t.Overlaps r))

theorem not_overlaps_not_covers' {t : PTlbEntry} {r : PRange} (h : ¬ t.Overlaps r)
    {v : Nat} (htv : t.covers v) (hrv : r.covers v) : False := by
  have h1 : t.vbase ≤ v ∧ v < t.vbase + t.vsize := htv
  have h2 : r.rb ≤ v ∧ v < r.rb + r.rs := hrv
  exact h ⟨by omega, by omega⟩

theorem mem_pflush {t : PTlbEntry} {tlb : List PTlbEntry} {r : PRange}
    (ht : t ∈ pflush tlb r) : t ∈ tlb ∧ ¬ t.Overlaps r := by
  simp only [pflush, List.mem_filter, decide_eq_true_eq] at ht
  exact ht

/-- `mprotect` actually changes the rights: a mapped granule of `r` now carries `np`. -/
theorem mprotect_sets_perms (m : PMapping) (r : PRange) (np : Perm) {v : Nat} {p : Perm}
    (hv : r.covers v) (hm : m v = some p) : (mprotectMap m r np) v = some np := by
  simp only [mprotectMap]
  split
  · rw [hm]; rfl
  · rename_i h; exact absurd hv h

/-- `mprotect` leaves everything outside `r` unchanged (the frame). -/
theorem mprotect_frame (m : PMapping) (r : PRange) (np : Perm) {v : Nat}
    (hv : ¬ r.covers v) : (mprotectMap m r np) v = m v := by
  simp only [mprotectMap]
  split
  · rename_i h; exact absurd h hv
  · rfl

/-- **`mprotect` preserves TLB coherence** (invariant 7, permission form): a surviving
entry does not overlap `r`, so the granule it caches is outside `r`, where the mapping
(hence its permissions) is unchanged — so the entry's cached perms still agree. -/
theorem mprotect_coherent (m : PMapping) (tlb : List PTlbEntry) (r : PRange) (np : Perm)
    (h : PTlbCoherent m tlb) :
    PTlbCoherent (mprotectMap m r np) (pflush tlb r) := by
  intro t ht v htv
  obtain ⟨htmem, hnov⟩ := mem_pflush ht
  have hvr : ¬ r.covers v := fun hrv => not_overlaps_not_covers' hnov htv hrv
  rw [mprotect_frame m r np hvr]
  exact h t htmem v htv

/-- **M2 — `mprotect` is correct.** With its flush: the new permissions take effect on
the mapped part of `r`, nothing outside `r` changes, and TLB coherence is
re-established. A flush-less `mprotect` fails the last conjunct — see below. -/
theorem mprotect_correct (m : PMapping) (tlb : List PTlbEntry) (r : PRange) (np : Perm)
    (h : PTlbCoherent m tlb) :
    (∀ v p, r.covers v → m v = some p → (mprotectMap m r np) v = some np) ∧
    (∀ v, ¬ r.covers v → (mprotectMap m r np) v = m v) ∧
    PTlbCoherent (mprotectMap m r np) (pflush tlb r) :=
  ⟨fun _ _ hv hm => mprotect_sets_perms m r np hv hm,
   fun _ hv => mprotect_frame m r np hv,
   mprotect_coherent m tlb r np h⟩

/-- **The forgotten flush is a provable error.** Granule 0 is mapped read-write and a
TLB entry caches that; `mprotect` write-protects it to read-only but omits the flush.
The stale read-write entry now contradicts the read-only mapping — coherence fails.
This is the §4 stale-permission use-after-protection-change made visible. -/
theorem mprotect_without_flush_breaks_coherence :
    ∃ (m : PMapping) (tlb : List PTlbEntry) (r : PRange) (np : Perm),
      PTlbCoherent m tlb ∧ ¬ PTlbCoherent (mprotectMap m r np) tlb := by
  refine ⟨(fun v => if v = 0 then some ⟨true, true, false⟩ else none),
          [⟨0, 1, ⟨true, true, false⟩⟩], ⟨0, 1⟩, ⟨true, false, false⟩, ?_, ?_⟩
  · -- coherent before: the cached read-write entry matches the read-write mapping at 0
    intro t ht v htv
    simp only [List.mem_singleton] at ht
    subst ht
    have hv0 : v = 0 := by
      have : (0 : Nat) ≤ v ∧ v < 0 + 1 := htv
      omega
    subst hv0
    rfl
  · -- not coherent after a flush-less write-protect: stale read-write entry over a
    -- now-read-only granule
    intro hcoh
    have h0 := hcoh ⟨0, 1, ⟨true, true, false⟩⟩ (by simp) 0 (by decide)
    exact absurd h0 (by decide)

end Tessera

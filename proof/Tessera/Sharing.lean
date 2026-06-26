/-
  Tessera — Layer A / M2: the shared backing object (Rung 2 of the abstraction
  ladder in ../doc/proof-obligations.md).

  A KAU's `c` per-`M` PTEs all resolve to **one backing object** (a `struct
  page`/folio in Linux). Its `mapcount`/`refcount` is therefore a **global**
  quantity — the count of mapping *sites* across all address spaces — maintained
  *incrementally* by add/remove operations. The pgcl catalog's #1/#5 bug class is
  exactly an incremental update whose delta does not match the true change in the
  site set (the Option-A-per-KAU vs Option-B-per-sub-PTE fracture; the
  migration restore/remove asymmetry) → the cached count drifts → underflow →
  free-while-mapped, or overflow → unreclaimable leak.

  This file models the discipline at the level the bug lives — the global count —
  while keeping a "site" **abstract** (`σ`). Concretely a site is later an
  `(address space, virtual granule)`, and the per-KAU-view contribution is
  `Kau.localMapcount` (Rung 1); committing to that structure (and to COW sharing
  groups) is Rung 3. Here the truth is the site *list* and the claim is the *cached
  count*; the well-formedness invariant `mapcount = |sites|` makes a mismatched delta
  a **provable error**, exactly as `Tlb.lean` does for the forgotten flush.
-/

namespace Tessera

/-- A **shared backing object**: the set of mapping `sites` (the truth) and the
cached `mapcount` (what code maintains incrementally). `σ` is the abstract site
type. -/
structure Backing (σ : Type) where
  sites    : List σ
  mapcount : Nat
deriving Repr

namespace Backing

/-- **Invariant (the refcount/mapcount discipline)**: the cached count equals the
true number of mapping sites. Its preservation is what forbids drift, hence
underflow (free-while-mapped) and overflow (unreclaimable leak). -/
def WF {σ : Type} (b : Backing σ) : Prop := b.mapcount = b.sites.length

/-- Add a batch of `sites` and bump the cached count by a *claimed* `delta`. The
correct discipline supplies `delta = ss.length`. -/
def add {σ : Type} (b : Backing σ) (ss : List σ) (delta : Nat) : Backing σ :=
  ⟨ss ++ b.sites, b.mapcount + delta⟩

/-- Remove `k` sites and decrement the cached count by a *claimed* `delta`. The
correct discipline supplies `delta = k` (with `k ≤ |sites|`). -/
def remove {σ : Type} (b : Backing σ) (k : Nat) (delta : Nat) : Backing σ :=
  ⟨b.sites.drop k, b.mapcount - delta⟩

/-- **Correct add preserves the invariant**: bumping by exactly the batch size keeps
`mapcount = |sites|`. -/
theorem add_wf {σ : Type} {b : Backing σ} (h : b.WF) (ss : List σ) :
    (b.add ss ss.length).WF := by
  have h' : b.mapcount = b.sites.length := h
  show b.mapcount + ss.length = (ss ++ b.sites).length
  rw [List.length_append]; omega

/-- **Correct remove preserves the invariant**: decrementing by exactly the number
removed keeps `mapcount = |sites|`. -/
theorem remove_wf {σ : Type} {b : Backing σ} (h : b.WF) {k : Nat}
    (hk : k ≤ b.sites.length) : (b.remove k k).WF := by
  have h' : b.mapcount = b.sites.length := h
  show b.mapcount - k = (b.sites.drop k).length
  rw [List.length_drop]; omega

/-- **The reclamation safety property**: under the discipline, the object's count is
zero **iff** it is truly unmapped. So you can never reclaim a still-mapped object
(free-while-mapped, pgcl #1/#7) and never strand a count above an empty site set
(unreclaimable leak, pgcl #6). -/
theorem free_iff_unmapped {σ : Type} {b : Backing σ} (h : b.WF) :
    b.mapcount = 0 ↔ b.sites = [] := by
  have h' : b.mapcount = b.sites.length := h
  rw [h']
  cases b.sites with
  | nil => simp
  | cons x xs => simp

/-- **Add/remove symmetry**: a correctly-counted add followed by its matching remove
returns the cached count to where it started — no drift (the property the migration
restore/remove asymmetry, pgcl #6, violated). -/
theorem add_remove_mapcount {σ : Type} (b : Backing σ) (ss : List σ) :
    ((b.add ss ss.length).remove ss.length ss.length).mapcount = b.mapcount := by
  show (b.mapcount + ss.length) - ss.length = b.mapcount
  omega

/-- **The under/over-count bug is a provable error.** If an `add` bumps the cached
count by a delta that does not match the number of sites it actually adds — the
Option-A-per-KAU vs Option-B-per-sub-PTE fracture (pgcl #5) — the invariant breaks.
Here adding 4 sites while claiming 1 leaves `mapcount = 1 ≠ 4 = |sites|`. -/
theorem add_wrong_delta_breaks_wf :
    ∃ (b : Backing Nat) (ss : List Nat) (delta : Nat),
      b.WF ∧ delta ≠ ss.length ∧ ¬ (b.add ss delta).WF := by
  refine ⟨⟨[], 0⟩, [1, 2, 3, 4], 1, ?_, ?_, ?_⟩
  · simp only [Backing.WF]; decide
  · decide
  · simp only [Backing.WF, Backing.add]; decide

/-- **Asymmetric add/remove drifts the count → leak.** Adding 4 sites (delta 4) then
removing them while decrementing by only 1 leaves `mapcount = 3` over an empty site
set: the object is unreclaimable though truly unmapped (the pgcl #6 shape). The
invariant catches it. -/
theorem asymmetric_add_remove_drifts :
    ∃ (b : Backing Nat) (ss : List Nat),
      b.WF ∧ ¬ ((b.add ss ss.length).remove ss.length 1).WF := by
  refine ⟨⟨[], 0⟩, [1, 2, 3, 4], ?_, ?_⟩
  · simp only [Backing.WF]; decide
  · simp only [Backing.WF, Backing.add, Backing.remove]; decide

end Backing

end Tessera

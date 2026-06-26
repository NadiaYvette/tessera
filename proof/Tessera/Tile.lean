/-
  Tessera — Layer A / M2 category E: promote / demote under HETEROGENEOUS tiling.

  Tiling-policy decision (../doc/intra-kau-tiling.md): **heterogeneous** — a KAU's
  mapping may be a *mix* of eligible page sizes (a "witch's brew"), modeled as a list
  of `Tile`s of varying sizes. Each tile is one hardware/superpage entry carrying a
  *single* coarse `(perms, dirty, ref)` for its whole span. The defining subtlety this
  choice takes on: a tile larger than `M` tracks dirty/referenced at *its* size, not
  per-`M`, so the resolution within a tile is coarsened. The accounting must be honest:

    * **promote** combines tiles → it must **aggregate** dirty/ref by OR (peeking one
      sub-tile's bit, the pgcl #20 failure, loses dirtiness);
    * **demote** splits a tile → it must **propagate** the coarse bits to *every*
      sub-tile (clearing them would silently drop a pending writeback → data loss);
    * both must preserve the per-KAU dirty-OR (invariant 5 under heterogeneous tiling).

  This file proves those, and shows a dirty-dropping demote and a peeking promote are
  provable errors. The TLB obligation for demote (flush the replaced superpage entry)
  is discharged by the size-aware flush already proven in `Tlb.lean` / `Mprotect.lean`.
  Deferred: the structural well-formedness of a heterogeneous tiling (disjoint, aligned,
  eligible-sized tiles) as a refinement of the per-`M` vector of `Kau.lean`.
-/
import Tessera.Basic

namespace Tessera

/-- A **tile**: one hardware entry covering `[base, base+size)` with uniform
permissions and a *single* coarse dirty/referenced bit for the whole span. A KAU's
mapping, under heterogeneous tiling, is a `List Tile` of possibly-differing sizes. -/
structure Tile where
  base  : Nat
  size  : Nat
  perms : Perm
  dirty : Bool
  ref   : Bool
  frame : Nat  -- physical frame of `base`; granule `v` maps to physical frame `frame + (v - base)`
deriving DecidableEq, Repr

/-- Lower half of a buddy demote: half the size, **inheriting** the coarse bits. -/
def Tile.demoteL (t : Tile) : Tile := { t with size := t.size / 2 }

/-- Upper half of a buddy demote: shifted base, half the size, inheriting the coarse
bits — and its physical frame **shifted by the same offset** so the per-granule
translation `frame + (v - base)` is preserved (the pgcl #9 correctness). -/
def Tile.demoteR (t : Tile) : Tile :=
  { t with base := t.base + t.size / 2, size := t.size / 2, frame := t.frame + t.size / 2 }

/-- **demote**: split a tile into its two halves, each carrying the parent's coarse
`(perms, dirty, ref)` — conservative propagation. -/
def Tile.demote (t : Tile) : List Tile := [t.demoteL, t.demoteR]

/-- **promote**: combine two tiles into one of the summed size, **aggregating** the
coarse bits by OR (and taking the left's perms — sound under `Promotable`). -/
def Tile.promote (a b : Tile) : Tile :=
  { base := a.base, size := a.size + b.size, perms := a.perms,
    dirty := a.dirty || b.dirty, ref := a.ref || b.ref, frame := a.frame }

/-- Promotion precondition (invariant 3, superpage uniformity, buddy case): adjacent,
equal-sized, identically-permissioned tiles. -/
def Tile.Promotable (a b : Tile) : Prop :=
  b.base = a.base + a.size ∧ a.size = b.size ∧ a.perms = b.perms

/-- **demote propagates conservatively**: every sub-tile carries the parent's dirty
and referenced bits — no granule that was under a dirty tile becomes clean. -/
theorem demote_conservative (t : Tile) :
    ∀ s ∈ t.demote, s.dirty = t.dirty ∧ s.ref = t.ref := by
  intro s hs
  simp only [Tile.demote, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- **demote preserves the dirty bit (no lost writeback)**: the OR over the two halves
equals the parent's dirty. A demote that cleared the bit would lose dirtiness. -/
theorem demote_dirty_or (t : Tile) : (t.demote).any (·.dirty) = t.dirty := by
  simp [Tile.demote, Tile.demoteL, Tile.demoteR]

/-- **promote aggregates dirty by OR** (the honest aggregation — not a peek). -/
theorem promote_dirty_or (a b : Tile) : (Tile.promote a b).dirty = (a.dirty || b.dirty) := rfl

/-- **promote aggregates referenced by OR**. -/
theorem promote_ref_or (a b : Tile) : (Tile.promote a b).ref = (a.ref || b.ref) := rfl

/-- Under the precondition, the promoted tile is uniform (its perms are the common
permissions of both). -/
theorem promote_uniform {a b : Tile} (h : Tile.Promotable a b) :
    (Tile.promote a b).perms = a.perms ∧ (Tile.promote a b).perms = b.perms := by
  obtain ⟨_, _, hp⟩ := h
  exact ⟨rfl, hp⟩

/-- **demote tiles its parent**: the halves are adjacent and cover `[base, base+size)`
exactly (invariant 4, the tiling). -/
theorem demote_cover (t : Tile) (hs : ∃ k, t.size = 2 ^ (k + 1)) :
    t.demoteL.base = t.base ∧
    t.demoteL.base + t.demoteL.size = t.demoteR.base ∧
    t.demoteR.base + t.demoteR.size = t.base + t.size := by
  obtain ⟨k, hk⟩ := hs
  have he : t.size = 2 * 2 ^ k := by rw [hk, Nat.pow_succ]; omega
  refine ⟨rfl, rfl, ?_⟩
  simp only [Tile.demoteR, Tile.demoteL]
  omega

/-- **promote is the exact inverse of demote** (invariant 4, soundness of split/merge):
re-combining the two halves recovers the original tile — geometry *and* coarse bits,
since the OR of the two inherited bits is the parent's bit. -/
theorem promote_demote (t : Tile) (hs : ∃ k, t.size = 2 ^ (k + 1)) :
    Tile.promote t.demoteL t.demoteR = t := by
  obtain ⟨k, hk⟩ := hs
  have he : t.size = 2 * 2 ^ k := by rw [hk, Nat.pow_succ]; omega
  have hsz : t.size / 2 + t.size / 2 = t.size := by omega
  simp only [Tile.promote, Tile.demoteL, Tile.demoteR, hsz, Bool.or_self]

/-- **Invariant 5 under heterogeneous tiling — promote preserves the per-KAU
dirty-OR**: replacing two tiles by their promotion does not change whether the KAU is
dirty. -/
theorem promote_preserves_kau_dirty (a b : Tile) (rest : List Tile) :
    (Tile.promote a b :: rest).any (·.dirty) = (a :: b :: rest).any (·.dirty) := by
  simp only [List.any_cons, Tile.promote, Bool.or_assoc]

/-- **Invariant 5 under heterogeneous tiling — demote preserves the per-KAU
dirty-OR**: replacing a tile by its two halves does not change whether the KAU is
dirty. -/
theorem demote_preserves_kau_dirty (t : Tile) (rest : List Tile) :
    (t.demote ++ rest).any (·.dirty) = (t :: rest).any (·.dirty) := by
  simp only [Tile.demote, List.any_append, List.any_cons, List.any_nil,
             Tile.demoteL, Tile.demoteR, Bool.or_self, Bool.or_false]

/-! ### The coarsening bugs as provable errors -/

/-- A **buggy demote** that clears the dirty bit on the halves. -/
def Tile.demoteBuggy (t : Tile) : List Tile :=
  [{ t.demoteL with dirty := false }, { t.demoteR with dirty := false }]

/-- Clearing dirty on demote loses dirtiness: the OR drops to `false` though the tile
was dirty — a silently-dropped writeback (data loss). A provable error. -/
theorem demoteBuggy_loses_dirty :
    ∃ t : Tile, t.dirty = true ∧ (t.demoteBuggy).any (·.dirty) ≠ t.dirty := by
  refine ⟨⟨0, 2, ⟨true, true, false⟩, true, false, 0⟩, rfl, ?_⟩
  decide

/-- A **buggy promote** that takes only the first sub-tile's dirty bit (the pgcl #20
"peek slot 0"). -/
def Tile.promoteBuggy (a b : Tile) : Tile := { Tile.promote a b with dirty := a.dirty }

/-- Peeking one bit on promote loses the other's dirtiness — the aggregate disagrees
with the true OR. A provable error. -/
theorem promoteBuggy_loses_dirty :
    ∃ a b : Tile, (Tile.promoteBuggy a b).dirty ≠ (a.dirty || b.dirty) := by
  refine ⟨⟨0, 1, ⟨true, true, false⟩, false, false, 0⟩,
          ⟨1, 1, ⟨true, true, false⟩, true, false, 1⟩, ?_⟩
  decide

end Tessera

/-
  Tessera — Layer A / M2 category E: structural well-formedness of a heterogeneous
  tiling, and its preservation by `demote`.

  A KAU's mapping, under the chosen heterogeneous regime, is a `List Tile` of mixed
  eligible sizes (`Tile.lean`). For it to be a faithful mapping the tiles must be
  **disjoint, aligned, and power-of-two sized** — exactly the well-formedness M1 (`WF`,
  `Split.lean`) already established for `Extent`s. A `Tile` is an `Extent` plus the two
  coarse bits, so we reuse M1 wholesale: a tile's geometry *is* its extent's, `demote`
  on a tile *is* the buddy `split` on its extent, and so "demote preserves the tiling's
  well-formedness" reduces to `WF_split_at`.

  (The dual — `promote`/merge preserves well-formedness under the buddy-alignment
  precondition — is the symmetric statement and is left as the next addition.)
-/
import Tessera.Split
import Tessera.Tile

namespace Tessera

/-- The `Extent` a tile occupies (its geometry, dropping the coarse dirty/ref bits). -/
def Tile.toExtent (t : Tile) : Extent := ⟨t.base, t.size, t.perms⟩

/-- A tile's `demote` is exactly the buddy `split` of its extent. -/
theorem Tile.demote_toExtent (t : Tile) :
    (t.demote).map Tile.toExtent = (t.toExtent).split := rfl

/-- **Well-formedness of a heterogeneous tiling**: the tiles, as extents, are
pairwise disjoint and each aligned and power-of-two sized (invariant 1, lifted to
tiles). -/
def TilingWF (tiles : List Tile) : Prop := WF (tiles.map Tile.toExtent)

/-- **`demote` preserves the tiling's well-formedness** (invariant 4, structural):
replacing any tile of a well-formed tiling by its two halves keeps the tiling
well-formed — because, as extents, this is exactly a buddy split, and M1's
`WF_split_at` applies. -/
theorem TilingWF.demote {pre post : List Tile} {t : Tile}
    (h : TilingWF (pre ++ t :: post)) (hs : ∃ k, t.size = 2 ^ (k + 1)) :
    TilingWF (pre ++ t.demote ++ post) := by
  unfold TilingWF at h ⊢
  rw [List.map_append, List.map_append, Tile.demote_toExtent]
  rw [List.map_append, List.map_cons] at h
  exact WF_split_at h hs

/-- The merge precondition (invariant 3 + buddy alignment): adjacent, equal-size,
identically-permissioned tiles whose combined extent is aligned to its size. -/
def Tile.MergeOK (a b : Tile) : Prop := Tile.Promotable a b ∧ (a.size + b.size) ∣ a.base

/-- **`promote` preserves the tiling's well-formedness** (invariant 4, the merge dual
of `TilingWF.demote`): replacing two `MergeOK` tiles by their promotion keeps the
tiling well-formed.  Reuses M1's `WF_merge_at`, mirroring how `demote` reuses
`WF_split_at`. -/
theorem TilingWF.promote {pre post : List Tile} {a b : Tile}
    (hwf : TilingWF (pre ++ a :: b :: post)) (hm : Tile.MergeOK a b) :
    TilingWF (pre ++ Tile.promote a b :: post) := by
  obtain ⟨⟨hadj, hsz, hperm⟩, halign⟩ := hm
  have hmem_a : a.toExtent ∈ (pre ++ a :: b :: post).map Tile.toExtent :=
    List.mem_map_of_mem _ (List.mem_append.mpr (Or.inr (List.mem_cons_self a (b :: post))))
  obtain ⟨⟨k, hak0⟩, _⟩ := hwf.1 a.toExtent hmem_a
  have hak : a.size = 2 ^ k := hak0
  have hhalf : (a.size + b.size) / 2 = a.size := by rw [← hsz]; omega
  have hmv : (Tile.promote a b).toExtent.Valid := by
    refine ⟨⟨k + 1, ?_⟩, ?_⟩
    · show a.size + b.size = 2 ^ (k + 1)
      rw [← hsz, hak, Nat.pow_succ]; omega
    · show a.size + b.size ∣ a.base
      exact halign
  have hms : (Tile.promote a b).toExtent.Splittable :=
    ⟨k, by show a.size + b.size = 2 ^ (k + 1); rw [← hsz, hak, Nat.pow_succ]; omega⟩
  have hsL : (Tile.promote a b).toExtent.splitL = a.toExtent := by
    simp only [Extent.splitL, Tile.promote, Tile.toExtent, hhalf]
  have hsR : (Tile.promote a b).toExtent.splitR = b.toExtent := by
    simp only [Extent.splitR, Tile.promote, Tile.toExtent, hhalf]
    rw [hadj, ← hsz, ← hperm]
  have hsplit : (Tile.promote a b).toExtent.split = [a.toExtent, b.toExtent] := by
    show [(Tile.promote a b).toExtent.splitL, (Tile.promote a b).toExtent.splitR] = _
    rw [hsL, hsR]
  unfold TilingWF
  rw [List.map_append, List.map_cons]
  apply WF_merge_at _ hmv hms
  rw [hsplit]
  have hrw : pre.map Tile.toExtent ++ [a.toExtent, b.toExtent] ++ post.map Tile.toExtent
           = (pre ++ a :: b :: post).map Tile.toExtent := by
    simp [List.map_append, List.map_cons]
  rw [hrw]
  exact hwf

end Tessera

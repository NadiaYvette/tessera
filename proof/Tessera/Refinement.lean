/-
  Tessera — M3: refinement / ABI-preservation (the headline).

  The central claim (kickoff §0, §8/M3): clustering and superpaging are **invisible to
  the ABI**. The ABI sees only the per-granule view — *which permissions does virtual
  granule `v` carry?* We model that view as `Tile.grants t v p` ("tile `t` maps granule
  `v` with permissions `p`") and prove it is unchanged by the representation choice:

    * `demote_grants` — a tile grants exactly what its demotion (into two sub-tiles, or
      ultimately `M`-entries) grants. The ABI cannot tell a superpage from its
      demotion.
    * `promote_grants` — under the uniformity precondition, two tiles grant exactly
      what their promotion grants. The ABI cannot tell individual entries from the
      superpage they form.
    * `demote_tiling_grants` / `promote_tiling_grants` — the same over a whole
      heterogeneous tiling (`TilingGrants`): the per-granule permission relation the
      mapping induces is invariant under promote/demote anywhere in it.

  This is the formal core of "the ABI cannot tell whether a region is superpage-mapped,
  individually mapped, or (with `none` for absent granules) partially populated." It is
  the M3 seed; the full S ⟸ A refinement layers a Layer-S `Mapping` on top of
  `TilingGrants` and relates it to the extent set of `Basic.lean`.
-/
import Tessera.Tile

namespace Tessera

/-- The ABI-visible fact: tile `t` maps virtual granule `v` with permissions `p`. -/
def Tile.grants (t : Tile) (v : Nat) (p : Perm) : Prop :=
  t.base ≤ v ∧ v < t.base + t.size ∧ t.perms = p

/-- **Superpaging is invisible (demote):** a tile grants a granule exactly the
permissions one of its two halves does. Demoting a superpage into sub-tiles (down to
`M`-entries) does not change the per-granule permission the ABI observes. -/
theorem demote_grants (t : Tile) (hs : ∃ k, t.size = 2 ^ (k + 1)) (v : Nat) (p : Perm) :
    t.grants v p ↔ (t.demoteL.grants v p ∨ t.demoteR.grants v p) := by
  obtain ⟨k, hk⟩ := hs
  have he : t.size = 2 * 2 ^ k := by rw [hk, Nat.pow_succ]; omega
  simp only [Tile.grants, Tile.demoteL, Tile.demoteR]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hlt : v < t.base + t.size / 2
    · exact Or.inl ⟨h1, hlt, h3⟩
    · exact Or.inr ⟨by omega, by omega, h3⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1, by omega, h3⟩
    · exact ⟨by omega, by omega, h3⟩

/-- **Superpaging is invisible (promote):** under the uniformity precondition, two
tiles grant a granule exactly what their promotion does. Forming a superpage from
individual entries does not change the per-granule permission the ABI observes. -/
theorem promote_grants {a b : Tile} (h : Tile.Promotable a b) (v : Nat) (p : Perm) :
    (Tile.promote a b).grants v p ↔ (a.grants v p ∨ b.grants v p) := by
  obtain ⟨hadj, hsz, hperm⟩ := h
  simp only [Tile.grants, Tile.promote]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hlt : v < a.base + a.size
    · exact Or.inl ⟨h1, hlt, h3⟩
    · exact Or.inr ⟨by omega, by omega, by rw [← hperm]; exact h3⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨h1, by omega, h3⟩
    · exact ⟨by omega, by omega, by rw [hperm]; exact h3⟩

/-- The permissions a whole tiling grants a granule: some tile in it does. -/
def TilingGrants (tiles : List Tile) (v : Nat) (p : Perm) : Prop :=
  ∃ t ∈ tiles, t.grants v p

/-- **Superpaging is invisible over a whole tiling (demote):** demoting any one tile of
a heterogeneous tiling leaves the per-granule permission relation the mapping induces
unchanged. -/
theorem demote_tiling_grants {pre post : List Tile} {t : Tile}
    (hs : ∃ k, t.size = 2 ^ (k + 1)) (v : Nat) (p : Perm) :
    TilingGrants (pre ++ t.demote ++ post) v p ↔ TilingGrants (pre ++ t :: post) v p := by
  constructor
  · rintro ⟨s, hmem, hg⟩
    rcases List.mem_append.mp hmem with h1 | hq
    · rcases List.mem_append.mp h1 with hp | hd
      · exact ⟨s, List.mem_append.mpr (Or.inl hp), hg⟩
      · have ht : t.grants v p := by
          apply (demote_grants t hs v p).mpr
          simp only [Tile.demote, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · exact Or.inl hg
          · exact Or.inr hg
        exact ⟨t, List.mem_append.mpr (Or.inr (List.mem_cons_self t post)), ht⟩
    · exact ⟨s, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem t hq)), hg⟩
  · rintro ⟨s, hmem, hg⟩
    rcases List.mem_append.mp hmem with hp | hcons
    · exact ⟨s, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))), hg⟩
    · rcases List.mem_cons.mp hcons with heq | hq
      · rcases (demote_grants t hs v p).mp (heq ▸ hg) with hgL | hgR
        · exact ⟨t.demoteL,
            List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_cons_self _ _)))), hgL⟩
        · exact ⟨t.demoteR,
            List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
              (List.mem_cons_of_mem _ (List.mem_cons_self _ _))))), hgR⟩
      · exact ⟨s, by simp [hq], hg⟩

/-- **Superpaging is invisible over a whole tiling (promote):** promoting two adjacent
uniform tiles leaves the per-granule permission relation unchanged. -/
theorem promote_tiling_grants {pre post : List Tile} {a b : Tile}
    (h : Tile.Promotable a b) (v : Nat) (p : Perm) :
    TilingGrants (pre ++ Tile.promote a b :: post) v p ↔ TilingGrants (pre ++ a :: b :: post) v p := by
  constructor
  · rintro ⟨s, hmem, hg⟩
    rcases List.mem_append.mp hmem with hp | hcons
    · exact ⟨s, List.mem_append.mpr (Or.inl hp), hg⟩
    · rcases List.mem_cons.mp hcons with rfl | hq
      · rcases (promote_grants h v p).mp hg with hga | hgb
        · exact ⟨a, List.mem_append.mpr (Or.inr (List.mem_cons_self a (b :: post))), hga⟩
        · exact ⟨b, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem a (List.mem_cons_self b post))), hgb⟩
      · exact ⟨s, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))), hg⟩
  · rintro ⟨s, hmem, hg⟩
    rcases List.mem_append.mp hmem with hp | hcons
    · exact ⟨s, List.mem_append.mpr (Or.inl hp), hg⟩
    · rcases List.mem_cons.mp hcons with heq | hcons2
      · exact ⟨Tile.promote a b, List.mem_append.mpr (Or.inr (List.mem_cons_self _ post)),
               (promote_grants h v p).mpr (Or.inl (heq ▸ hg))⟩
      · rcases List.mem_cons.mp hcons2 with heq2 | hq
        · exact ⟨Tile.promote a b, List.mem_append.mpr (Or.inr (List.mem_cons_self _ post)),
                 (promote_grants h v p).mpr (Or.inr (heq2 ▸ hg))⟩
        · exact ⟨s, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hq)), hg⟩

end Tessera

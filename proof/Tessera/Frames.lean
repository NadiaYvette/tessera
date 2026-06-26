/-
  Tessera — M3 with physical frames: Layer S as VA → (physical frame, permissions).

  `Refinement.lean`/`RefinementS.lean` made the *permission* mapping invisible to the
  representation. This file does the same for the **physical translation**, completing
  Layer S to the full `VA → (PA, perm)` the kickoff §2 specifies. The ABI-visible fact
  is now `Tile.grantsF t v f p` — *tile `t` maps virtual granule `v` to physical frame
  `f` with permissions `p`* — where the physical frame is the *linear* `t.frame +
  (v - t.base)`.

  Two results, both the heart of real superpage correctness:

    * `demote_grantsF` — a tile maps each granule to exactly the (frame, perm) its
      demotion does. Crucially, `demoteR` shifts its frame by the same offset as its
      base, so the per-granule physical address is preserved. A demote that *forgot*
      to shift the frame would re-point the upper half's granules to the wrong physical
      pages — exactly the pgcl #9 (arm64 contpte fold) bug, here a non-theorem.
    * `promote_grantsF` — under `PromotableF` (the buddy precondition **plus physical
      contiguity** `b.frame = a.frame + a.size`), two tiles map each granule to exactly
      what their promotion does. The contiguity hypothesis is the real
      superpage-promotion precondition (telix/pgcl check it); without it the merged
      superpage's single linear translation cannot agree with the two pieces.

  Tiling-level versions (`*_tiling_grantsF`) lift these over a whole heterogeneous
  tiling, exactly as in `Refinement.lean`.
-/
import Tessera.Tile

namespace Tessera

/-- The full ABI-visible fact: tile `t` maps virtual granule `v` to physical frame `f`
with permissions `p`. The physical frame is the linear `t.frame + (v - t.base)`. -/
def Tile.grantsF (t : Tile) (v f : Nat) (p : Perm) : Prop :=
  t.base ≤ v ∧ v < t.base + t.size ∧ t.frame + (v - t.base) = f ∧ t.perms = p

/-- Physical promotion precondition: `Promotable` **plus physical contiguity** — the
upper tile's physical range begins exactly where the lower's ends. -/
def Tile.PromotableF (a b : Tile) : Prop := Tile.Promotable a b ∧ b.frame = a.frame + a.size

/-- **Superpaging invisible, with physical frames (demote).** A tile maps each granule
to exactly the (frame, perm) one of its halves does — the upper half's frame shift
preserving the per-granule physical address. -/
theorem demote_grantsF (t : Tile) (hs : ∃ k, t.size = 2 ^ (k + 1)) (v f : Nat) (p : Perm) :
    t.grantsF v f p ↔ (t.demoteL.grantsF v f p ∨ t.demoteR.grantsF v f p) := by
  obtain ⟨k, hk⟩ := hs
  have he : t.size = 2 * 2 ^ k := by rw [hk, Nat.pow_succ]; omega
  simp only [Tile.grantsF, Tile.demoteL, Tile.demoteR]
  constructor
  · rintro ⟨h1, h2, hf, hp⟩
    by_cases hlt : v < t.base + t.size / 2
    · exact Or.inl ⟨h1, hlt, hf, hp⟩
    · exact Or.inr ⟨by omega, by omega, by omega, hp⟩
  · rintro (⟨h1, h2, hf, hp⟩ | ⟨h1, h2, hf, hp⟩)
    · exact ⟨h1, by omega, hf, hp⟩
    · exact ⟨by omega, by omega, by omega, hp⟩

/-- **Superpaging invisible, with physical frames (promote).** Under buddy adjacency
*and physical contiguity*, two tiles map each granule to exactly what their promotion
does. -/
theorem promote_grantsF {a b : Tile} (h : Tile.PromotableF a b) (v f : Nat) (p : Perm) :
    (Tile.promote a b).grantsF v f p ↔ (a.grantsF v f p ∨ b.grantsF v f p) := by
  obtain ⟨⟨hadj, hsz, hperm⟩, hframe⟩ := h
  simp only [Tile.grantsF, Tile.promote]
  constructor
  · rintro ⟨h1, h2, hf, hp⟩
    by_cases hlt : v < a.base + a.size
    · exact Or.inl ⟨h1, hlt, hf, hp⟩
    · exact Or.inr ⟨by omega, by omega, by omega, by rw [← hperm]; exact hp⟩
  · rintro (⟨h1, h2, hf, hp⟩ | ⟨h1, h2, hf, hp⟩)
    · exact ⟨h1, by omega, hf, hp⟩
    · exact ⟨by omega, by omega, by omega, by rw [hperm]; exact hp⟩

/-- The (frame, perm) a whole tiling grants a granule: some tile in it does. -/
def TilingGrantsF (tiles : List Tile) (v f : Nat) (p : Perm) : Prop :=
  ∃ t ∈ tiles, t.grantsF v f p

/-- **Physical-frame refinement over a tiling (demote).** -/
theorem demote_tiling_grantsF {pre post : List Tile} {t : Tile}
    (hs : ∃ k, t.size = 2 ^ (k + 1)) (v f : Nat) (p : Perm) :
    TilingGrantsF (pre ++ t.demote ++ post) v f p ↔ TilingGrantsF (pre ++ t :: post) v f p := by
  constructor
  · rintro ⟨s, hmem, hg⟩
    rcases List.mem_append.mp hmem with h1 | hq
    · rcases List.mem_append.mp h1 with hp | hd
      · exact ⟨s, List.mem_append.mpr (Or.inl hp), hg⟩
      · have ht : t.grantsF v f p := by
          apply (demote_grantsF t hs v f p).mpr
          simp only [Tile.demote, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · exact Or.inl hg
          · exact Or.inr hg
        exact ⟨t, List.mem_append.mpr (Or.inr (List.mem_cons_self t post)), ht⟩
    · exact ⟨s, by simp [hq], hg⟩
  · rintro ⟨s, hmem, hg⟩
    rcases List.mem_append.mp hmem with hp | hcons
    · exact ⟨s, List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))), hg⟩
    · rcases List.mem_cons.mp hcons with heq | hq
      · rcases (demote_grantsF t hs v f p).mp (heq ▸ hg) with hgL | hgR
        · exact ⟨t.demoteL,
            List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (List.mem_cons_self _ _)))), hgL⟩
        · exact ⟨t.demoteR,
            List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
              (List.mem_cons_of_mem _ (List.mem_cons_self _ _))))), hgR⟩
      · exact ⟨s, by simp [hq], hg⟩

/-- **Physical-frame refinement over a tiling (promote).** -/
theorem promote_tiling_grantsF {pre post : List Tile} {a b : Tile}
    (h : Tile.PromotableF a b) (v f : Nat) (p : Perm) :
    TilingGrantsF (pre ++ Tile.promote a b :: post) v f p ↔
      TilingGrantsF (pre ++ a :: b :: post) v f p := by
  constructor
  · rintro ⟨s, hmem, hg⟩
    rcases List.mem_append.mp hmem with hp | hcons
    · exact ⟨s, List.mem_append.mpr (Or.inl hp), hg⟩
    · rcases List.mem_cons.mp hcons with heq | hq
      · rcases (promote_grantsF h v f p).mp (heq ▸ hg) with hga | hgb
        · exact ⟨a, List.mem_append.mpr (Or.inr (List.mem_cons_self a (b :: post))), hga⟩
        · exact ⟨b, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem a (List.mem_cons_self b post))), hgb⟩
      · exact ⟨s, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))), hg⟩
  · rintro ⟨s, hmem, hg⟩
    rcases List.mem_append.mp hmem with hp | hcons
    · exact ⟨s, List.mem_append.mpr (Or.inl hp), hg⟩
    · rcases List.mem_cons.mp hcons with heq | hcons2
      · exact ⟨Tile.promote a b, List.mem_append.mpr (Or.inr (List.mem_cons_self _ post)),
               (promote_grantsF h v f p).mpr (Or.inl (heq ▸ hg))⟩
      · rcases List.mem_cons.mp hcons2 with heq2 | hq
        · exact ⟨Tile.promote a b, List.mem_append.mpr (Or.inr (List.mem_cons_self _ post)),
                 (promote_grantsF h v f p).mpr (Or.inr (heq2 ▸ hg))⟩
        · exact ⟨s, List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hq)), hg⟩

end Tessera

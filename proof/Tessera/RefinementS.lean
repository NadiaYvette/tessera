/-
  Tessera — M3: the full S ⟸ A refinement (ABI-preservation), completed.

  `Refinement.lean` proved superpaging invisible at the level of the grants *relation*.
  Here we close the refinement to Layer S — the ABI as a genuine partial function
  `Mapping := Nat → Option Perm`:

    * `TilingGrants_functional` — under well-formedness (disjoint tiles), the grants
      relation is **single-valued**: a granule is granted at most one permission. So the
      Layer-S object the representation induces is a well-defined *function*, not just a
      relation. (This is where disjointness — invariant 1 — earns its keep.)
    * `tilingMapping` — that induced Layer-S partial function, and
      `tilingMapping_eq_some_iff` — it *is* the grants relation (under WF).
    * `tilingMapping_demote` / `tilingMapping_promote` — the induced Layer-S mapping is
      **invariant under promote/demote**. This is the refinement: the Layer-A
      representation may be re-tiled however it likes (one superpage, individual
      `M`-entries, any heterogeneous mix), and the Layer-S mapping the ABI sees does not
      move. Clustering and superpaging are invisible to the ABI — the kickoff §0
      top-level theorem, at the tiling layer.
-/
import Tessera.Refinement
import Tessera.Tiling

namespace Tessera

private theorem functional_aux : ∀ (tiles : List Tile), TilingWF tiles →
    ∀ (v : Nat) (p q : Perm), TilingGrants tiles v p → TilingGrants tiles v q → p = q := by
  intro tiles
  induction tiles with
  | nil => intro _ v p q hp _; simp [TilingGrants] at hp
  | cons t rest ih =>
    intro hwf v p q hp hq
    have hwfE : WF (Tile.toExtent t :: rest.map Tile.toExtent) := hwf
    obtain ⟨hval, hpw⟩ := hwfE
    rw [List.pairwise_cons] at hpw
    obtain ⟨hdisj, hpwR⟩ := hpw
    have hwfR : TilingWF rest := ⟨fun x hx => hval x (List.mem_cons_of_mem _ hx), hpwR⟩
    rcases hp with ⟨a, ha, hga⟩
    rcases hq with ⟨b, hb, hgb⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨_, _, hpp⟩ := hga; obtain ⟨_, _, hqq⟩ := hgb; rw [← hpp, ← hqq]
      · exfalso
        obtain ⟨h1, h2, _⟩ := hga; obtain ⟨h3, h4, _⟩ := hgb
        have hd : Disjoint (Tile.toExtent a) (Tile.toExtent b) :=
          hdisj _ (List.mem_map_of_mem _ hb')
        simp only [Disjoint, Extent.lo, Extent.hi, Tile.toExtent] at hd
        omega
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exfalso
        obtain ⟨h1, h2, _⟩ := hga; obtain ⟨h3, h4, _⟩ := hgb
        have hd : Disjoint (Tile.toExtent b) (Tile.toExtent a) :=
          hdisj _ (List.mem_map_of_mem _ ha')
        simp only [Disjoint, Extent.lo, Extent.hi, Tile.toExtent] at hd
        omega
      · exact ih hwfR v p q ⟨a, ha', hga⟩ ⟨b, hb', hgb⟩

/-- **The Layer-S object is well-defined.** Under well-formedness, the grants relation
a tiling induces is single-valued: a granule carries at most one permission. -/
theorem TilingGrants_functional {tiles : List Tile} (hwf : TilingWF tiles) {v : Nat} {p q : Perm}
    (hp : TilingGrants tiles v p) (hq : TilingGrants tiles v q) : p = q :=
  functional_aux tiles hwf v p q hp hq

open Classical in
/-- The **Layer-S mapping** the tiling induces: virtual granule `v` ↦ the (unique, under
WF) permission granted there, or `none`. This is the ABI's view as a partial function. -/
noncomputable def tilingMapping (tiles : List Tile) (v : Nat) : Option Perm :=
  if h : ∃ p, TilingGrants tiles v p then some (Classical.choose h) else none

/-- The induced Layer-S mapping **is** the grants relation (under WF). -/
theorem tilingMapping_eq_some_iff {tiles : List Tile} (hwf : TilingWF tiles) (v : Nat) (p : Perm) :
    tilingMapping tiles v = some p ↔ TilingGrants tiles v p := by
  unfold tilingMapping
  by_cases h : ∃ p, TilingGrants tiles v p
  · rw [dif_pos h]
    constructor
    · intro heq
      have hc : Classical.choose h = p := Option.some.inj heq
      rw [← hc]; exact Classical.choose_spec h
    · intro hg
      have hc : Classical.choose h = p := TilingGrants_functional hwf (Classical.choose_spec h) hg
      rw [hc]
  · rw [dif_neg h]
    constructor
    · intro heq; simp at heq
    · intro hg; exact absurd ⟨p, hg⟩ h

/-- Two well-formed tilings inducing the same grants relation induce the same Layer-S
mapping. -/
theorem tilingMapping_congr {l1 l2 : List Tile} (hwf1 : TilingWF l1) (hwf2 : TilingWF l2)
    (v : Nat) (hgr : ∀ p, TilingGrants l1 v p ↔ TilingGrants l2 v p) :
    tilingMapping l1 v = tilingMapping l2 v := by
  rcases h1 : tilingMapping l1 v with _ | p
  · rcases h2 : tilingMapping l2 v with _ | q
    · rfl
    · exfalso
      have hg2 : TilingGrants l2 v q := (tilingMapping_eq_some_iff hwf2 v q).mp h2
      have hg1 : TilingGrants l1 v q := (hgr q).mpr hg2
      rw [(tilingMapping_eq_some_iff hwf1 v q).mpr hg1] at h1
      exact Option.noConfusion h1
  · have hg1 : TilingGrants l1 v p := (tilingMapping_eq_some_iff hwf1 v p).mp h1
    have hg2 : TilingGrants l2 v p := (hgr p).mp hg1
    rw [(tilingMapping_eq_some_iff hwf2 v p).mpr hg2]

/-- **The refinement (demote):** demoting any tile leaves the Layer-S mapping the ABI
sees unchanged. -/
theorem tilingMapping_demote {pre post : List Tile} {t : Tile} (hs : ∃ k, t.size = 2 ^ (k + 1))
    (hwf1 : TilingWF (pre ++ t.demote ++ post)) (hwf2 : TilingWF (pre ++ t :: post)) (v : Nat) :
    tilingMapping (pre ++ t.demote ++ post) v = tilingMapping (pre ++ t :: post) v :=
  tilingMapping_congr hwf1 hwf2 v (fun p => demote_tiling_grants hs v p)

/-- **The refinement (promote):** promoting two adjacent uniform tiles leaves the
Layer-S mapping the ABI sees unchanged. -/
theorem tilingMapping_promote {pre post : List Tile} {a b : Tile} (h : Tile.Promotable a b)
    (hwf1 : TilingWF (pre ++ Tile.promote a b :: post)) (hwf2 : TilingWF (pre ++ a :: b :: post))
    (v : Nat) :
    tilingMapping (pre ++ Tile.promote a b :: post) v = tilingMapping (pre ++ a :: b :: post) v :=
  tilingMapping_congr hwf1 hwf2 v (fun p => promote_tiling_grants h v p)

end Tessera

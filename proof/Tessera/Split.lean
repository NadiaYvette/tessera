/-
  Tessera — Layer A: the `split` operation and the M1 theorem.

  See ../doc/tessera-verification-kickoff.md §8 (M1), §9.

  M1: define `split`; prove it preserves well-formedness.  This is the core data
  model and the whole technique in miniature: pure data, structural reasoning, no
  TLB yet (the hardware-state obligations enter in M2).

  `split` here is the canonical **buddy halving**: an extent of size `2^(k+1)` is
  cut into two adjacent, equally-sized, identically-permissioned halves of size
  `2^k` that tile it.  The headline result is `WF_split_at`: replacing any extent
  of a well-formed set by its two halves yields a well-formed set.
-/
import Tessera.Basic

namespace Tessera
namespace Extent

/-- An extent is **splittable** (by buddy halving) when its size is at least two
granules — i.e. `2^(k+1)` for some `k`.  A single-granule extent (size `2^0 = 1`)
is minimal and cannot be split further. -/
def Splittable (e : Extent) : Prop := ∃ k : Nat, e.size = 2 ^ (k + 1)

/-- The lower half of a buddy split: same base, half the size, same permissions. -/
def splitL (e : Extent) : Extent :=
  { base := e.base, size := e.size / 2, perms := e.perms }

/-- The upper half of a buddy split: base shifted by half the size, half the
size, same permissions. -/
def splitR (e : Extent) : Extent :=
  { base := e.base + e.size / 2, size := e.size / 2, perms := e.perms }

/-- **Buddy split**: an extent of size `2^(k+1)` into its two halves of size
`2^k`, which together tile it exactly (`split_cover`). -/
def split (e : Extent) : List Extent := [e.splitL, e.splitR]

/-- A splittable extent's size is `2·2^k` and its half is `2^k`. -/
theorem size_half {e : Extent} (h : e.Splittable) :
    ∃ k, e.size = 2 * 2 ^ k ∧ e.size / 2 = 2 ^ k := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [hk, Nat.pow_succ]; omega, by rw [hk, Nat.pow_succ]; omega⟩

/-- The lower half of a valid, splittable extent is itself valid: its size is the
power of two `2^k`, and its base (unchanged) stays aligned because `2^k ∣ 2^(k+1)`
divides the old base. -/
theorem splitL_valid {e : Extent} (hv : e.Valid) (hs : e.Splittable) :
    e.splitL.Valid := by
  obtain ⟨k, hsz, hhalf⟩ := size_half hs
  obtain ⟨_, halign⟩ := hv
  have h2k : (2 : Nat) ^ k ∣ e.base := Nat.dvd_trans ⟨2, by rw [hsz]; omega⟩ halign
  refine ⟨⟨k, ?_⟩, ?_⟩
  · show e.size / 2 = 2 ^ k
    exact hhalf
  · show e.size / 2 ∣ e.base
    rw [hhalf]; exact h2k

/-- The upper half of a valid, splittable extent is itself valid: its size is
`2^k`, and its base `e.base + 2^k` is aligned because `2^k` divides both summands. -/
theorem splitR_valid {e : Extent} (hv : e.Valid) (hs : e.Splittable) :
    e.splitR.Valid := by
  obtain ⟨k, hsz, hhalf⟩ := size_half hs
  obtain ⟨_, halign⟩ := hv
  have h2k : (2 : Nat) ^ k ∣ e.base := Nat.dvd_trans ⟨2, by rw [hsz]; omega⟩ halign
  refine ⟨⟨k, ?_⟩, ?_⟩
  · show e.size / 2 = 2 ^ k
    exact hhalf
  · show e.size / 2 ∣ e.base + e.size / 2
    rw [hhalf]
    obtain ⟨m, hm⟩ := h2k
    exact ⟨m + 1, by rw [hm, Nat.mul_succ]⟩

/-- The two halves are disjoint: the lower half ends exactly where the upper half
begins. -/
theorem split_disjoint {e : Extent} : Disjoint e.splitL e.splitR := by
  simp only [Disjoint, Extent.lo, Extent.hi, splitL, splitR]; omega

/-- Each half lies inside the parent's interval, so it inherits disjointness from
anything the parent is disjoint from (lower half). -/
theorem splitL_disjoint_of {e f : Extent} (h : Disjoint e f) : Disjoint e.splitL f := by
  simp only [Disjoint, Extent.lo, Extent.hi, splitL] at h ⊢; omega

/-- Each half lies inside the parent's interval, so it inherits disjointness from
anything the parent is disjoint from (upper half). -/
theorem splitR_disjoint_of {e f : Extent} (h : Disjoint e f) : Disjoint e.splitR f := by
  simp only [Disjoint, Extent.lo, Extent.hi, splitR] at h ⊢; omega

/-- Converse of `split{L,R}_disjoint_of`: an extent is disjoint from `f` if both its
halves are (the union of the halves is the parent).  Needs `f` nonempty so a
zero-width `f` sitting on the split boundary cannot sneak between the halves. -/
theorem merge_disjoint {e f : Extent} (hs : e.Splittable) (hf : 0 < f.size)
    (hL : Disjoint e.splitL f) (hR : Disjoint e.splitR f) : Disjoint e f := by
  obtain ⟨k, hsz, hhalf⟩ := size_half hs
  simp only [Disjoint, Extent.lo, Extent.hi, splitL, splitR] at hL hR ⊢
  omega

/-- **Tiling** (kickoff invariant 4): the two halves cover the parent exactly —
the lower half starts at the parent's low end, the halves meet, and the upper half
ends at the parent's high end.  "The union of the sub-extents is the original." -/
theorem split_cover {e : Extent} (hs : e.Splittable) :
    e.splitL.lo = e.lo ∧ e.splitL.hi = e.splitR.lo ∧ e.splitR.hi = e.hi := by
  obtain ⟨k, hsz, hhalf⟩ := size_half hs
  refine ⟨rfl, rfl, ?_⟩
  show e.base + e.size / 2 + e.size / 2 = e.base + e.size
  omega

end Extent

/-- **M1 — `split` preserves well-formedness (general position).**

Given a well-formed extent set written as `pre ++ e :: post` and a splittable
`e`, replacing `e` in place by its two buddy halves yields a well-formed set
`pre ++ e.split ++ post`.  The decomposition into `pre`/`post` is without loss of
generality (a set has no intrinsic order), so this is the statement "splitting any
extent of a well-formed set preserves well-formedness."

The proof's content is exactly what the brief wants exercised: the halves are
valid (alignment + power-of-two sizing survive halving), the halves are disjoint
from each other, and — the set-level crux — because each half lies within the
parent's interval, the halves stay disjoint from every other extent the parent was
disjoint from. -/
theorem WF_split_at {pre post : List Extent} {e : Extent}
    (hwf : WF (pre ++ e :: post)) (hs : e.Splittable) :
    WF (pre ++ e.split ++ post) := by
  obtain ⟨hval, hpw⟩ := hwf
  have hmem_e : e ∈ pre ++ e :: post :=
    List.mem_append.mpr (Or.inr (List.mem_cons_self e post))
  have hev : e.Valid := hval e hmem_e
  rw [List.pairwise_append] at hpw
  obtain ⟨hpre_pw, hcons_pw, hcross⟩ := hpw
  rw [List.pairwise_cons] at hcons_pw
  obtain ⟨he_post, hpost_pw⟩ := hcons_pw
  have hLv := Extent.splitL_valid hev hs
  have hRv := Extent.splitR_valid hev hs
  refine ⟨?_, ?_⟩
  · -- Every extent of `pre ++ e.split ++ post` is valid.
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hxq
    · rcases List.mem_append.mp hx1 with hxp | hxs
      · exact hval x (List.mem_append.mpr (Or.inl hxp))
      · rcases (show x = e.splitL ∨ x = e.splitR by simpa [Extent.split] using hxs) with rfl | rfl
        · exact hLv
        · exact hRv
    · exact hval x (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem e hxq)))
  · -- The whole list is pairwise disjoint.
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨hpre_pw, ?_, ?_⟩, hpost_pw, ?_⟩
    · -- the two halves are pairwise disjoint
      show ([e.splitL, e.splitR]).Pairwise Disjoint
      refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
      · intro a' ha'; rw [List.mem_singleton] at ha'; subst ha'; exact Extent.split_disjoint
      · intro a' ha'; exact absurd ha' (List.not_mem_nil a')
    · -- every `pre` extent is disjoint from each half
      intro a ha b hb
      have haE : Disjoint a e := hcross a ha e (List.mem_cons_self e post)
      rcases (show b = e.splitL ∨ b = e.splitR by simpa [Extent.split] using hb) with rfl | rfl
      · exact (Extent.splitL_disjoint_of haE.symm).symm
      · exact (Extent.splitR_disjoint_of haE.symm).symm
    · -- every `pre ++ split` extent is disjoint from each `post` extent
      intro a ha b hb
      rcases List.mem_append.mp ha with hap | has
      · exact hcross a hap b (List.mem_cons_of_mem e hb)
      · rcases (show a = e.splitL ∨ a = e.splitR by simpa [Extent.split] using has) with rfl | rfl
        · exact Extent.splitL_disjoint_of (he_post b hb)
        · exact Extent.splitR_disjoint_of (he_post b hb)

/-- **M1 (head form).**  The common case of `WF_split_at`: splitting the first
extent of a well-formed set.  Stated separately because it reads as the plain
"`split` preserves `WF`." -/
theorem WF_split_cons {e : Extent} {rest : List Extent}
    (hwf : WF (e :: rest)) (hs : e.Splittable) :
    WF (e.split ++ rest) := by
  have h := WF_split_at (pre := []) (post := rest) (e := e) hwf hs
  simpa using h

/-- **Merge preserves well-formedness** — the converse of `WF_split_at`, completing
invariant 4 (consistent split/merge).  If the split-form `pre ++ e.split ++ post` is
well-formed and `e` is a valid splittable extent, then merging the two halves back
into `e` keeps the set well-formed.  The crux is the dual of `WF_split_at`'s: each
neighbour disjoint from *both* halves is disjoint from their union `e`
(`merge_disjoint`). -/
theorem WF_merge_at {pre post : List Extent} {e : Extent}
    (hwf : WF (pre ++ e.split ++ post)) (hv : e.Valid) (hs : e.Splittable) :
    WF (pre ++ e :: post) := by
  obtain ⟨hval, hpw⟩ := hwf
  rw [List.pairwise_append, List.pairwise_append] at hpw
  obtain ⟨⟨hpre_pw, _, hpre_split⟩, hpost_pw, hcross⟩ := hpw
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hp | hcons
    · exact hval x (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))))
    · rcases List.mem_cons.mp hcons with rfl | hq
      · exact hv
      · exact hval x (List.mem_append.mpr (Or.inr hq))
  · rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨hpre_pw, ⟨?_, hpost_pw⟩, ?_⟩
    · intro x hx
      have hLx : Disjoint e.splitL x := hcross e.splitL (by simp [Extent.split]) x hx
      have hRx : Disjoint e.splitR x := hcross e.splitR (by simp [Extent.split]) x hx
      exact Extent.merge_disjoint hs (hval x (List.mem_append.mpr (Or.inr hx))).size_pos hLx hRx
    · intro a ha b hb
      rcases List.mem_cons.mp hb with heq | hq
      · rw [heq]
        have hLa : Disjoint a e.splitL := hpre_split a ha e.splitL (by simp [Extent.split])
        have hRa : Disjoint a e.splitR := hpre_split a ha e.splitR (by simp [Extent.split])
        have ha_pos : 0 < a.size :=
          (hval a (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ha))))).size_pos
        exact (Extent.merge_disjoint hs ha_pos hLa.symm hRa.symm).symm
      · exact hcross a (List.mem_append.mpr (Or.inl ha)) b hq

/-! ### Smoke tests / worked examples -/

/-- An 8-granule extent at base 0 (read-write) is splittable: `8 = 2^(2+1)`. -/
example : (Extent.mk 0 8 ⟨true, true, false⟩).Splittable := ⟨2, rfl⟩

/-- That extent is valid: power-of-two size, base aligned. -/
example : (Extent.mk 0 8 ⟨true, true, false⟩).Valid := ⟨⟨3, rfl⟩, ⟨0, rfl⟩⟩

/-- A singleton well-formed set splits to a well-formed pair. -/
example : WF (Extent.split (Extent.mk 0 8 ⟨true, true, false⟩)) := by
  have hwf : WF [Extent.mk 0 8 ⟨true, true, false⟩] :=
    ⟨by intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact ⟨⟨3, rfl⟩, ⟨0, rfl⟩⟩,
     List.pairwise_singleton _ _⟩
  have h := WF_split_cons hwf ⟨2, rfl⟩
  simpa using h

end Tessera

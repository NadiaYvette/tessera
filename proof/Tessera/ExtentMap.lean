/-
  Tessera — Layer I (first rung): the **ordered extent map** — the semantic model of
  telix's `mm/extent.rs` B+-tree, refined against the Layer-A extent set (`Basic.lean`).

  A B+-tree keyed by base address *is* an ordered map; its observable content is the
  in-order sequence of (base → extent), kept sorted and non-overlapping.  We model that
  content directly: a `List Extent` with the **ordering invariant**
  `Ordered = Pairwise (earlier.hi ≤ later.lo)`.  This is STRICTER than Layer-A `WF`
  (which only requires `Pairwise Disjoint`, unordered) — it adds the key order the tree
  maintains.  The refinement theorems below show:

    * the tree's ordering invariant **implies** Layer-A well-formedness
      (`WFI_imp_WF`) — the representation is sound w.r.t. the algorithm's invariant;
    * `lookup` (find the covering extent) is correct against the induced mapping
      (`lookup_sound`, `lookup_complete`);
    * `insert` (ordered insertion) **refines** the set-add (`insert_mem`) and
      **preserves** the ordering invariant when the new extent is disjoint
      (`insert_ordered`) — while inserting an *overlapping* extent provably breaks it
      (`insert_overlap_breaks`, the telix #14 / pgcl #14 overlap bug).

  The node fanout / balancing of an actual B+-tree is a further, performance-only
  refinement *of this model* (an ordered map either way), and is left to a later rung.
-/
import Tessera.Basic

namespace Tessera
namespace ExtentMap

/-- The **ordering invariant** of the extent map: extents sorted by position and
consecutively non-overlapping — each earlier extent ends at or before each later one
begins.  This is the B+-tree's key-ordering invariant. -/
def Ordered (es : List Extent) : Prop := es.Pairwise (fun a b => a.hi ≤ b.lo)

/-- **The refinement of the disjointness invariant**: ordered-and-non-overlapping
implies pairwise-disjoint (the ordered relation is the left disjunct of `Disjoint`). -/
theorem ordered_imp_disjoint {es : List Extent} (h : Ordered es) : es.Pairwise Disjoint :=
  h.imp (fun hab => Or.inl hab)

/-- **Concrete (Layer-I) well-formedness**: every extent valid, and the ordering
invariant holds. -/
def WFI (es : List Extent) : Prop := (∀ e ∈ es, e.Valid) ∧ Ordered es

/-- **The headline refinement**: the extent map's invariant implies the Layer-A extent-set
invariant.  So anything the map maintains is a legitimate Layer-A state — the
representation is *sound* w.r.t. the verified algorithm. -/
theorem WFI_imp_WF {es : List Extent} (h : WFI es) : WF es :=
  ⟨h.1, ordered_imp_disjoint h.2⟩

/-! ### The induced mapping and `lookup` -/

/-- The Layer-A mapping the representation induces: `va` is mapped iff some extent
covers it. -/
def covers (es : List Extent) (va : Nat) : Prop := ∃ e ∈ es, e.lo ≤ va ∧ va < e.hi

/-- **Lookup**: find the extent covering `va` (the tree's point query). -/
def lookup (es : List Extent) (va : Nat) : Option Extent :=
  es.find? (fun x => decide (x.lo ≤ va ∧ va < x.hi))

/-- **Lookup is sound**: a hit is a real, covering member of the map. -/
theorem lookup_sound {es : List Extent} {va : Nat} {e : Extent}
    (h : lookup es va = some e) : e ∈ es ∧ e.lo ≤ va ∧ va < e.hi := by
  rw [lookup] at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨hmem, hp⟩

/-- **Lookup is complete**: if the induced mapping covers `va`, the query finds a hit
(so the representation faithfully answers the mapping). -/
theorem lookup_complete {es : List Extent} {va : Nat} (h : covers es va) :
    (lookup es va).isSome := by
  obtain ⟨e, he, hlo, hhi⟩ := h
  rw [Option.isSome_iff_ne_none]
  intro hnone
  rw [lookup, List.find?_eq_none] at hnone
  have hbad := hnone e he
  simp [hlo, hhi] at hbad

/-! ### `insert` and its refinement -/

/-- **Insert** an extent into the ordered map, keeping it sorted by base. -/
def insert (e : Extent) : List Extent → List Extent
  | [] => [e]
  | f :: fs => if e.base ≤ f.base then e :: f :: fs else f :: insert e fs

/-- **Insert refines the set-add**: the map after insert is exactly the old contents
plus the new extent. -/
theorem insert_mem {e x : Extent} {es : List Extent} :
    x ∈ insert e es ↔ x = e ∨ x ∈ es := by
  induction es with
  | nil => simp [insert]
  | cons f fs ih =>
      simp only [insert]
      by_cases hle : e.base ≤ f.base
      · rw [if_pos hle]; simp only [List.mem_cons]
      · rw [if_neg hle, List.mem_cons, ih, List.mem_cons]
        constructor
        · rintro (rfl | rfl | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
        · rintro (rfl | rfl | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)

/-- Helper: if `e` starts at or before a valid `f` and they are disjoint, then `e` lies
entirely before `f`. -/
theorem before_of_le {e f : Extent} (hf : f.Valid) (hle : e.base ≤ f.base)
    (hd : Disjoint e f) : e.hi ≤ f.lo := by
  have := hf.size_pos
  simp only [Disjoint, Extent.lo, Extent.hi] at hd ⊢; omega

/-- Helper: if a valid `e` starts strictly after `f` and they are disjoint, then `f`
lies entirely before `e`. -/
theorem before_of_gt {e f : Extent} (he : e.Valid) (hgt : f.base < e.base)
    (hd : Disjoint e f) : f.hi ≤ e.lo := by
  have := he.size_pos
  simp only [Disjoint, Extent.lo, Extent.hi] at hd ⊢; omega

/-- **Insert preserves the ordering invariant** when the new extent is valid and disjoint
from every extent in the (ordered, valid) map.  This is the heart of "the B+-tree insert
keeps the tree well-formed." -/
theorem insert_ordered {e : Extent} (hv : e.Valid) :
    ∀ {es : List Extent}, (∀ f ∈ es, f.Valid) → Ordered es → (∀ f ∈ es, Disjoint e f) →
      Ordered (insert e es)
  | [], _, _, _ => by simp [insert, Ordered]
  | f :: fs, hvs, ho, hd => by
      have hvf : f.Valid := hvs f (List.mem_cons_self f fs)
      have ho' : Ordered fs := (List.pairwise_cons.mp ho).2
      have hhead : ∀ g ∈ fs, f.hi ≤ g.lo := (List.pairwise_cons.mp ho).1
      have hdf : Disjoint e f := hd f (List.mem_cons_self f fs)
      simp only [insert]
      by_cases hle : e.base ≤ f.base
      · rw [if_pos hle, Ordered, List.pairwise_cons]
        refine ⟨?_, ho⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hxfs
        · exact before_of_le hvf hle hdf
        · have hfx := hhead x hxfs
          have hxv : x.Valid := hvs x (List.mem_cons_of_mem f hxfs)
          have hxbase : e.base ≤ x.base := by
            simp only [Extent.lo, Extent.hi] at hfx; omega
          exact before_of_le hxv hxbase (hd x (List.mem_cons_of_mem f hxfs))
      · have hvs' : ∀ g ∈ fs, g.Valid := fun g hg => hvs g (List.mem_cons_of_mem f hg)
        have hd' : ∀ g ∈ fs, Disjoint e g := fun g hg => hd g (List.mem_cons_of_mem f hg)
        have ihf : Ordered (insert e fs) := insert_ordered hv hvs' ho' hd'
        rw [if_neg hle, Ordered, List.pairwise_cons]
        refine ⟨?_, ihf⟩
        intro x hx
        rcases insert_mem.mp hx with rfl | hxfs
        · exact before_of_gt hv (by omega) hdf
        · exact hhead x hxfs

/-- **Inserting an overlapping extent breaks the ordering invariant — a provable error**
(telix #14 / pgcl #14): placing `[2,6)` into a map already holding `[0,4)` yields
`[ [0,4), [2,6) ]`, where `4 ≤ 2` fails.  The disjointness precondition of
`insert_ordered` is necessary; an overlap must be split out first, not inserted. -/
theorem insert_overlap_breaks :
    ∃ (es : List Extent) (e : Extent), Ordered es ∧ ¬ Ordered (insert e es) := by
  refine ⟨[⟨0, 4, ⟨true, true, false⟩⟩], ⟨2, 4, ⟨true, true, false⟩⟩, ?_, ?_⟩
  · simp [Ordered]
  · intro hc
    rw [show insert (⟨2, 4, ⟨true, true, false⟩⟩ : Extent) [⟨0, 4, ⟨true, true, false⟩⟩]
          = [⟨0, 4, ⟨true, true, false⟩⟩, ⟨2, 4, ⟨true, true, false⟩⟩] from rfl] at hc
    rw [Ordered, List.pairwise_cons] at hc
    have hbad := hc.1 ⟨2, 4, ⟨true, true, false⟩⟩ (by simp)
    simp only [Extent.lo, Extent.hi] at hbad
    omega

end ExtentMap
end Tessera

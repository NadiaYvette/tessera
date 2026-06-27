/-
  Tessera — Layer I (rung 2): the **tree-node structure** of telix's `mm/extent.rs`
  B+-tree, refined onto the ordered extent map of `ExtentMap.lean` (hence onto Layer A).

  A B+-tree is a multi-level *search* tree; the branching factor and balancing are
  performance concerns.  Its *semantic* content — the obligation that matters for VM
  correctness — is: the in-order traversal yields a sorted, non-overlapping extent map,
  and the point query descends to the covering extent.  We model that with an ordered
  binary search tree of extents and prove:

    * `bst_ordered` — the search-tree invariant makes the in-order traversal `Ordered`
      (so, via `ExtentMap.WFI_imp_WF`, a well-formed tree is a well-formed Layer-A state);
    * `lookup_sound` — the tree's descend-by-key point query returns a genuine covering
      extent of the represented map.

  Composing `bst_ordered` with `ExtentMap.ordered_imp_disjoint` gives the full chain
  **tree ⟶ ordered map ⟶ Layer-A extent set.**  (Balancing / insert-with-split is a
  further performance-only refinement of *this* model.)
-/
import Tessera.ExtentMap

namespace Tessera
namespace BTree

/-- A search tree of extents — the node structure of the extent B+-tree. -/
inductive ExtentTree where
  | leaf : ExtentTree
  | node : ExtentTree → Extent → ExtentTree → ExtentTree

/-- In-order traversal: the ordered extent map the tree represents. -/
def toList : ExtentTree → List Extent
  | .leaf => []
  | .node l e r => toList l ++ e :: toList r

/-- The **search-tree invariant**: the left subtree lies entirely before the pivot, the
pivot entirely before the right subtree, recursively. -/
def BST : ExtentTree → Prop
  | .leaf => True
  | .node l e r =>
      BST l ∧ BST r ∧ (∀ x ∈ toList l, x.hi ≤ e.lo) ∧ (∀ x ∈ toList r, e.hi ≤ x.lo)

/-- **The tree refines the ordered map**: an in-order traversal of a search tree is
sorted and non-overlapping (`ExtentMap.Ordered`).  With `ExtentMap.WFI_imp_WF`, a
well-formed extent tree is therefore a well-formed Layer-A extent set. -/
theorem bst_ordered : ∀ {t : ExtentTree}, BST t → ExtentMap.Ordered (toList t)
  | .leaf, _ => by simp [toList, ExtentMap.Ordered]
  | .node l e r, h => by
      obtain ⟨hl, hr, hle, hre⟩ := h
      simp only [toList, ExtentMap.Ordered, List.pairwise_append, List.pairwise_cons]
      refine ⟨bst_ordered hl, ⟨hre, bst_ordered hr⟩, ?_⟩
      intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hbr
      · exact hle a ha
      · have h1 : a.hi ≤ e.lo := hle a ha
        have h2 : e.hi ≤ b.lo := hre b hbr
        simp only [Extent.lo, Extent.hi] at h1 h2 ⊢; omega

/-- **Lookup** descends by key to the covering extent. -/
def lookup (va : Nat) : ExtentTree → Option Extent
  | .leaf => none
  | .node l e r =>
      if va < e.lo then lookup va l
      else if e.hi ≤ va then lookup va r
      else some e

/-- **The tree lookup is sound**: a hit is a real, covering member of the represented
map — refining `ExtentMap.lookup_sound` to the tree structure. -/
theorem lookup_sound : ∀ {t : ExtentTree}, BST t → ∀ {va : Nat} {e : Extent},
    lookup va t = some e → e ∈ toList t ∧ e.lo ≤ va ∧ va < e.hi
  | .leaf, _, _, _, h => by simp [lookup] at h
  | .node l e' r, hbst, va, e, h => by
      obtain ⟨hl, hr, _, _⟩ := hbst
      simp only [lookup] at h
      split at h
      · obtain ⟨hmem, hcov⟩ := lookup_sound hl h
        exact ⟨by simp [toList, hmem], hcov⟩
      · split at h
        · obtain ⟨hmem, hcov⟩ := lookup_sound hr h
          exact ⟨by simp [toList, hmem], hcov⟩
        · rename_i hge hlt
          simp only [Option.some.injEq] at h
          subst h
          simp only [Extent.lo, Extent.hi] at hge hlt ⊢
          exact ⟨by simp [toList], by omega, by omega⟩

end BTree
end Tessera

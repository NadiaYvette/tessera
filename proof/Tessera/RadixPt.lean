/-
  Tessera — Layer I (rung): the **refcounted radix page-table subtree**, concretizing the
  bare shared node of `PtShare.lean` into a subtree that *carries the mappings it
  provides*.  An intermediate PT node and everything beneath it can be COW-shared across
  address spaces at once; that is why freeing such a subtree wrongly unmaps *many* VAs for
  *every* sibling (telix #2: `free_page_table_tree` freed the globally-shared Thread-region
  L2 still installed in every aspace).

  We model a subtree as `(rc, mappings)` — its share count and the leaf VAs it exposes —
  and prove:

    * `release_shared_survives` — releasing one sharer of a shared (`rc ≥ 2`) subtree
      leaves it referenced and its mappings intact (siblings keep every VA);
    * `free_shared_subtree_uaf` — an unconditional free of a still-shared subtree drops
      those mappings: a provable use-after-free (telix #2);
    * `node_release_preserves` — the discipline **composes up the radix tree**: a parent
      node exposes the same union of mappings after one sibling releases a shared child.
-/
import Tessera.PtShare

namespace Tessera
namespace RadixPt

/-- A shared **page-table subtree**: the number of address spaces / fork-groups that
reference it (`rc`), and the leaf VAs it maps (`mappings`, provided to every sharer). -/
structure Subtree where
  rc       : Nat
  mappings : List Nat
deriving Repr

namespace Subtree

/-- Release one sharer's reference (correct discipline: decrement; the content is
untouched and stays available to the remaining sharers). -/
def release (c : Subtree) : Subtree := ⟨c.rc - 1, c.mappings⟩

/-- The buggy **unconditional free** of a subtree (telix #2). -/
def freeUnchecked (_ : Subtree) : Subtree := ⟨0, []⟩

/-- **A shared subtree survives one release** (telix #2): with ≥ 2 sharers, one exiting
leaves the subtree referenced and intact — the siblings keep every VA it maps. -/
theorem release_shared_survives {c : Subtree} (h : 2 ≤ c.rc) :
    0 < (release c).rc ∧ (release c).mappings = c.mappings := by
  refine ⟨?_, rfl⟩
  show 0 < c.rc - 1; omega

/-- **Freeing a still-shared subtree is a use-after-free — a provable error** (telix #2):
it drops every mapping the subtree provided, though sibling address spaces still
reference it; their VAs are silently unmapped. -/
theorem free_shared_subtree_uaf :
    ∃ c : Subtree, 2 ≤ c.rc ∧ c.mappings ≠ [] ∧
      (freeUnchecked c).mappings ≠ c.mappings := by
  refine ⟨⟨2, [4096]⟩, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end Subtree

/-- A radix **node** exposes the union of its child subtrees' mappings. -/
def nodeMappings (children : List Subtree) : List Nat := children.flatMap Subtree.mappings

/-- **The refcount discipline composes up the tree**: releasing one sibling's reference to
a shared child leaves the parent node exposing exactly the same mappings — COW sharing is
correct at the radix level, not just per node. -/
theorem node_release_preserves (pre : List Subtree) (c : Subtree) (post : List Subtree)
    (h : 2 ≤ c.rc) :
    nodeMappings (pre ++ Subtree.release c :: post) = nodeMappings (pre ++ c :: post) := by
  have hm : Subtree.mappings (Subtree.release c) = Subtree.mappings c :=
    (Subtree.release_shared_survives h).2
  simp only [nodeMappings, List.flatMap_append, List.flatMap_cons, hm]

end RadixPt
end Tessera

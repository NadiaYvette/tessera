/-
  Tessera — Layer A / M2: Rung 3 — concrete sharing (proof-obligations.md ladder).
  Where Rung 2 (`Sharing.lean`) kept a "site" abstract, Rung 3 makes it concrete —
  `(address space, virtual granule)` — and adds the structural layer Rung 2 could not
  reach: **shared page-table nodes with their own refcounts** (telix `mm/ptshare.rs`).

  This is where invariant 6 "fully lives," and it catches the structural sharing bugs:

    * **#2** — aspace teardown freed the globally-shared Thread-region L2 PT subtree that
      every aspace still referenced → every Thread VA unmapped. A shared PT subtree must
      be **refcounted**: dropping one referrer while siblings remain must NOT free it.
    * **#19** — an orphaned shared marker (`rc > 0` but no owning fork/COW group) → a
      later map silently fails. Every shared marker must correspond to a live group.
    * **#20** — the **boundary overhang**: a shared PT node can cover ranges from more
      than one VMA / COW-group, so a *per-object* refcount mis-accounts it. The node's
      refcount must be over its own (cross-object) referrer set, not per-object.

  (Kernel-extent exclusion #1 and free-while-shared-object #8 are already done in
  `Fork.lean` / `Cow.lean`; this file is the PT-node-and-concrete-site complement.)
-/
import Tessera.Sharing

namespace Tessera

/-- Concrete site identifiers (Rung 3): an address space and a virtual granule. -/
abbrev AS := Nat
abbrev VAddr := Nat
abbrev Site := AS × VAddr

/-- The **COW group** (mapper set) of a backing object over concrete sites: the address
spaces that map it — the first component of each site. Forking adds an aspace; COW-break
removes one, so the group tracks exactly who shares (the relation Rung 2 left abstract). -/
def mappers (b : Backing Site) : List AS := b.sites.map Prod.fst

/-- Under the refcount discipline, the mapper list has exactly `mapcount` entries — one
per site. So "who shares" and "how many share" agree. -/
theorem mappers_length_wf {b : Backing Site} (h : b.WF) : (mappers b).length = b.mapcount := by
  show (b.sites.map Prod.fst).length = b.mapcount
  rw [List.length_map]; exact h.symm

/-- A **shared page-table node** (telix `mm/ptshare.rs`): the fork/COW `groups` that
reference it (its true, cross-object referrer set) and a cached refcount `rc`. A PT node
may be shared by groups spanning *different* backing objects / VMAs, so its refcount is
over its own referrer set, not a per-object count (telix #20). -/
structure PtNode where
  groups : List Nat   -- the referencing fork/COW groups (true referrer set)
  rc     : Nat        -- cached refcount
deriving Repr

namespace PtNode

/-- **Node refcount discipline** (invariant 6 for shared PT nodes): the cached refcount
equals the number of referencing groups. -/
def WF (n : PtNode) : Prop := n.rc = n.groups.length

/-- A new group references the node (a fork installs a shared marker). -/
def addRef (n : PtNode) (g : Nat) : PtNode := ⟨g :: n.groups, n.rc + 1⟩

/-- A group releases the node (COW-break / unmap). -/
def dropRef (n : PtNode) : PtNode := ⟨n.groups.drop 1, n.rc - 1⟩

/-- **Correct addRef preserves the discipline**: one new referrer, count +1. -/
theorem addRef_wf {n : PtNode} (h : n.WF) (g : Nat) : (n.addRef g).WF := by
  have h' : n.rc = n.groups.length := h
  show n.rc + 1 = (g :: n.groups).length
  simp only [List.length_cons]; omega

/-- **Correct dropRef preserves the discipline**: one referrer leaves, count −1. -/
theorem dropRef_wf {n : PtNode} (h : n.WF) (hpos : 1 ≤ n.groups.length) :
    (n.dropRef).WF := by
  have h' : n.rc = n.groups.length := h
  show n.rc - 1 = (n.groups.drop 1).length
  rw [List.length_drop]; omega

/-- **#2 — freeing a node still referenced by a sibling group is a use-after-free**
(telix #2: aspace teardown freed the globally-shared Thread-region L2). If ≥ 2 groups
reference the node, dropping one leaves the count positive — it must NOT be reclaimed. -/
theorem free_shared_node_strands_siblings {n : PtNode} (h : n.WF)
    (hge : 2 ≤ n.groups.length) : (n.dropRef).rc ≠ 0 := by
  have h' : n.rc = n.groups.length := h
  show n.rc - 1 ≠ 0
  omega

/-- **#19 — an orphaned shared marker is a provable error** (telix #19): a node marked
shared (`rc > 0`) but with no owning group breaks the discipline. Every shared marker
must correspond to a live group. -/
theorem orphan_marker_breaks_wf :
    ∃ n : PtNode, n.rc ≠ 0 ∧ n.groups = [] ∧ ¬ n.WF := by
  refine ⟨⟨[], 1⟩, by decide, rfl, ?_⟩
  intro hc; simp [PtNode.WF] at hc

/-- A **per-object** refcount: counts only referrers belonging to `objGroups` — the naïve
accounting telix #20 warns against. -/
def perObject (n : PtNode) (objGroups : List Nat) : Nat :=
  (n.groups.filter (fun g => decide (g ∈ objGroups))).length

/-- **#20 — the boundary overhang: a per-object refcount under-counts a node shared
across objects, so freeing on it is a use-after-free.** A PT node referenced by a group
from object B is invisible to object A's per-object count: A sees `perObject = 0` and
would free the node, yet its true `rc > 0` (B still references it). The node's refcount
must be over its own cross-object referrer set, not per-object (telix #20). -/
theorem overhang_undercounts :
    ∃ (n : PtNode) (objAGroups : List Nat),
      n.WF ∧ n.perObject objAGroups = 0 ∧ n.rc ≠ 0 := by
  exact ⟨⟨[7], 1⟩, [1, 2], rfl, by decide, by decide⟩

end PtNode

end Tessera

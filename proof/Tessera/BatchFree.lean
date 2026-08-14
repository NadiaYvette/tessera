/-
  Tessera — BATCHED-FREE cluster dedup (pgcl #143: the systemic double-free across EVERY batched
  free path).

  r5probe (2026-07-02) showed PGCL143-DOUBLEFREE's 1st-freers are all BATCHED frees:
  `tlb_remove_table_rcu` (the page-table RCU batch), `shrink_folio_list` (the reclaim batch),
  `folios_put_refs` (the gather / lru-drain batch), `rcu_do_batch`.  A pgcl cluster is ONE
  `struct page` spanning PAGE_MMUCOUNT (=16) sub-units; a batch may enqueue the same cluster
  once per sub-unit it touched, and a per-ENTRY free then frees that one struct page that many
  times => a double-free (freelist corruption, shared-page reuse -> int3/SIGSEGV/env clobber).

  The fix already applied to the GATHER path (`mm/swap_state.c free_pages_and_swap_cache`) is to
  DEDUPE: free each DISTINCT cluster exactly once.  This file models the invariant EVERY batched
  free path must satisfy -- the spec for the #143 sweep across tlb_remove_table_rcu / reclaim /
  lru-drain.
-/
namespace Tessera
namespace BatchFree

/-- A free batch = the list of cluster ids it will free, WITH multiplicity: one entry per
sub-unit the path enqueued.  A cluster's multiplicity is how many entries name it. -/
abbrev Batch := List Nat

/-- **BUGGY** free-per-ENTRY: a cluster is freed once per entry = `count` times. -/
def freesPerEntry (b : Batch) (c : Nat) : Nat := b.count c

/-- **FIXED** dedup free: each DISTINCT cluster is freed exactly once (the gather dedupe). -/
def freesDeduped (b : Batch) (c : Nat) : Nat := if b.contains c then 1 else 0

/-- **THE BUG**: a cluster the batch lists ≥2× (≥2 sub-units enqueued) is freed ≥2× -- the
double-free the detector caught for tlb_remove_table_rcu / shrink_folio_list / folios_put_refs. -/
theorem perEntry_double_frees (b : Batch) (c : Nat) (h : 2 ≤ b.count c) :
    2 ≤ freesPerEntry b c := h

/-- **THE FIX IS SAFE**: the deduped free frees any cluster AT MOST once -- never a double-free,
for ANY batch, at any multiplicity. -/
theorem deduped_never_double_frees (b : Batch) (c : Nat) : freesDeduped b c ≤ 1 := by
  unfold freesDeduped
  cases b.contains c <;> simp

/-- **THE FIX IS COMPLETE (no leak)**: a cluster present in the batch is freed EXACTLY once. -/
theorem deduped_frees_present_once (b : Batch) (c : Nat) (h : b.contains c = true) :
    freesDeduped b c = 1 := by
  unfold freesDeduped; rw [h]; decide

/-- **ABSENT ⇒ not freed** (dedup frees nothing spurious). -/
theorem deduped_absent_not_freed (b : Batch) (c : Nat) (h : b.contains c = false) :
    freesDeduped b c = 0 := by
  unfold freesDeduped; rw [h]; decide

/-! ### Concrete: a gapped cluster enqueued twice (two sub-units) double-frees per-entry -/

/-- A batch that touched two sub-units of cluster 7 (and one of cluster 9). -/
def gappedBatch : Batch := [7, 9, 7]

/-- Per-entry frees cluster 7 TWICE (the double-free); dedup frees it once. -/
theorem gapped_perEntry_vs_dedup :
    freesPerEntry gappedBatch 7 = 2 ∧ freesDeduped gappedBatch 7 = 1 := by
  decide

end BatchFree
end Tessera

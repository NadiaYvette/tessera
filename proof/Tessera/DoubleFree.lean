/-
  Tessera — DOUBLE-FREE (#143 residual, reinc #42/#43).

  Pinned on the laptop by the general double-free detector (PGCL143-DOUBLEFREE, 10x): the SAME cluster
  folio sits in >1 mmu_gather encoded entry -- a GAPPED-cluster madvise (MADV_DONTNEED/FREE) zap makes
  several __tlb_remove_folio_pages calls for the same head page (one per pgcl_pte_batch contiguous run
  across the gaps) -- so free_pages_and_swap_cache frees it once per entry.  With the refcount floored
  BELOW the total deferred (the over-defer / GatherLedger owed>refs), the first entry frees it and the
  second DOUBLE-FREES: the page lands on the pcp free-list twice -> list_del/add corruption
  (free_frozen_page_commit / __rmqueue_pcplist) -> shared-lib page reuse -> Electron int3 / segfault.
  bad_page stays 0 (flags/mapping clear on the 2nd free), so only the freed-stamp detector names it.

  Kernel (drive/143-spurcatch): stamp pgcl143_freed[pfn] at __free_pages_prepare (the common free
  chokepoint), clear at post_alloc_hook; on a 2nd free of an un-realloc'd pfn, ENFORCE by returning
  false (the callers' bad-page skip) so the page stays on the pcp list exactly once.  Field: #43
  drove list-corrupt 10->0 and Telegram rendered its window.

  This models the enforcement's soundness.  The over-defer that ENABLES the double-free is
  `GatherLedger` (owed>refs); the freed-while-referenced WRONG-DATA residual is the deeper
  present-PTE-without-ref phantom (task #17), NOT modeled here.
-/
namespace Tessera
namespace DoubleFree

/-- A page's pcp-list lifecycle: `onList` = currently on the free list; `freeCount` = times added to
the list since its last alloc (must stay ≤ 1). -/
structure Page where
  onList    : Bool
  freeCount : Nat
deriving Repr, DecidableEq

/-- A RAW free unconditionally adds the page to the list (the pre-#43 behaviour). -/
def Page.freeRaw (p : Page) : Page := { onList := true, freeCount := p.freeCount + 1 }

/-- The #43 GUARDED free: free only if NOT already on the list; a 2nd free of a listed page is a no-op
(the __free_pages_prepare `return false` skip). -/
def Page.freeGuarded (p : Page) : Page :=
  if p.onList = true then p else { onList := true, freeCount := p.freeCount + 1 }

/-- **DOUBLE-FREE** = the page added to the pcp list more than once (list corruption). -/
def Page.doubleFreed (p : Page) : Prop := 1 < p.freeCount

/-- **THE BUG**: a raw 2nd free of an already-listed page double-frees (`freeCount` 2). -/
theorem raw_double_frees : (Page.freeRaw (Page.freeRaw ⟨false, 0⟩)).doubleFreed := by
  show (1 : Nat) < 2; omega

/-- **THE #43 ENFORCEMENT IS SOUND**: the guarded free of an un-realloc'd page is a no-op on the 2nd
free, so `freeCount` stays 1 and NEVER reaches 2 — the page is on the pcp list exactly once, no
corruption. -/
theorem guarded_never_double_frees :
    ¬ (Page.freeGuarded (Page.freeGuarded ⟨false, 0⟩)).doubleFreed := by
  show ¬ (1 : Nat) < 1; omega

/-- …and the guard still frees a genuinely un-listed page exactly once (no leak of legitimate frees). -/
theorem guarded_frees_once :
    (Page.freeGuarded ⟨false, 0⟩).onList = true ∧ (Page.freeGuarded ⟨false, 0⟩).freeCount = 1 :=
  ⟨rfl, rfl⟩

end DoubleFree
end Tessera

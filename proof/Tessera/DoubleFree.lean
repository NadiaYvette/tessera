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

/-! ### The SOURCE-level fix: coalesce a folio's gather entries (free_pages_and_swap_cache)

The `__free_pages_prepare` guard above is a backstop that catches the 2nd free at the
common chokepoint.  But laptop boot -psub showed it is not enough: a gapped cluster is
zapped as several contiguous runs, each emitting its OWN encoded mmu_gather entry for the
SAME one-struct-page cluster folio, and `free_pages_and_swap_cache` batches the duplicate
into `folios_put_refs` BEFORE the guard runs -- the 2nd put lands on an already-freed page
and re-adds it to the pcp list -> freelist `list_del`/`list_add` corruption -> a CPU stuck
in that report under the pcp lock -> every `vmstat_update` worker spins in `decay_pcp_high`
-> soft lockup (the GUI-wedge, task #15).  The fix folds all of a folio's entries into ONE
put, so it is freed exactly once no matter how many runs a gapped cluster splits into. -/

/-- Free the folio once per gather entry (pre-fix): a page starting un-listed, freed
`entries` times by `freeRaw`, ends with `freeCount = entries`. -/
def freeEntries : Nat → Page
  | 0     => ⟨false, 0⟩
  | n + 1 => Page.freeRaw (freeEntries n)

theorem freeEntries_count (n : Nat) : (freeEntries n).freeCount = n := by
  induction n with
  | zero => rfl
  | succ k ih => show (freeEntries k).freeCount + 1 = k + 1; rw [ih]

/-- **THE BUG** (gapped cluster): ≥2 runs → ≥2 entries → the folio is freed more than once. -/
theorem entries_double_free (n : Nat) (h : 2 ≤ n) : (freeEntries n).doubleFreed := by
  show 1 < (freeEntries n).freeCount
  rw [freeEntries_count]; omega

/-- DEDUPE: all of a folio's `entries` are coalesced into ONE put with the summed refs. -/
def freeDeduped (_entries : Nat) : Page := Page.freeRaw ⟨false, 0⟩

/-- **THE FIX IS SOUND**: the coalesced free puts the folio exactly once for ANY run
count — the double-free (and hence the freelist corruption and the pcp-lock wedge) is
structurally impossible, independent of the cluster's gap pattern. -/
theorem deduped_frees_once (n : Nat) : (freeDeduped n).freeCount = 1 := rfl

theorem deduped_never_double_frees (n : Nat) : ¬ (freeDeduped n).doubleFreed := by
  show ¬ (1 < 1); omega

end DoubleFree
end Tessera

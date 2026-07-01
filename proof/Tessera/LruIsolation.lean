/-
  Tessera — LRU-ISOLATION: the #143 RESIDUAL (freed-while-on-LRU; `active|swapbacked` set at free).

  After the count-side fix closed the reincarnation UAF (kernel `bad_page` 7–50 → 0–1/boot, verified in
  the laptop journal 2026-07-01), ONE residual real `bad_page` remains (boot −1, pfn 0x53d0e):

      refcount:0 mapcount:0   (counts CLEAN — no phantom, exactly what GatherLedger's audit found)
      flags: uptodate|active|swapbacked   PAGE_FLAGS_CHECK_AT_FREE   ts > free_ts (reused)
      free path: free_unref_folios ← folios_put_refs ← folio_batch_move_lru ← __folio_batch_add_and_move

  A page reached the freelist while still LRU-FLAGGED.  This is NOT a refcount phantom — the counts
  balance.  It is a lifecycle/ORDERING bug: the per-cpu LRU-add batch defers the flag maintenance, and if
  the last reference is dropped (the batch drain's `folios_put_refs`) BEFORE the LRU flags are cleared,
  the page is freed still flagged.  The obligation is `isolate-then-free`: clear the at-free flags (remove
  from the LRU) before the ref reaches 0.  A Property-2-flavored ordering property, distinct from
  `GatherLedger`'s static count balance — modeled here so the residual's invariant is explicit.

  (1/boot, near the noise floor; a single `bad_page` leaks one page and continues, it does not kill init.)
-/
namespace Tessera
namespace LruIsolation

/-- A folio in the free/LRU lifecycle.  `refs` = refcount; `flagged` = the LRU state flags that MUST be
clear at free (`active|swapbacked|lru`, the `PAGE_FLAGS_CHECK_AT_FREE` set). -/
structure Folio where
  refs    : Nat
  flagged : Bool
deriving Repr, DecidableEq

/-- Isolate: remove from the LRU, clearing the at-free flags. -/
def Folio.isolate (f : Folio) : Folio := { f with flagged := false }

/-- Drop a reference (the batch drain's `put`); the page is freed when it hits 0. -/
def Folio.put (f : Folio) : Folio := { f with refs := f.refs - 1 }

/-- Freed = the refcount reached 0. -/
def Folio.freed (f : Folio) : Prop := f.refs = 0

/-- **THE OBLIGATION — isolate before free**: whenever the folio is freed it is not LRU-flagged. -/
def Folio.SafeFree (f : Folio) : Prop := f.freed → f.flagged = false

instance (f : Folio) : Decidable f.SafeFree := by
  unfold Folio.SafeFree Folio.freed; infer_instance

/-- Once isolated, EVERY free is safe (the flag is clear, whatever the refcount does). -/
theorem isolate_safeFree (f : Folio) : (f.isolate).SafeFree := by
  intro _; rfl

/-- `put` preserves an already-clear flag — so isolate-then-put keeps it clear through the free. -/
theorem put_preserves_unflagged (f : Folio) (h : f.flagged = false) : (f.put).flagged = false := by
  simp only [Folio.put, h]

/-- **CORRECT DRAIN — isolate THEN drop the last ref**: the freed page is unflagged.  Safe. -/
theorem isolate_then_put_safe (f : Folio) : ((f.isolate).put).SafeFree :=
  fun _ => put_preserves_unflagged _ rfl

/-- **THE BUG — drop the last ref while still flagged**: the page is freed with `active|swapbacked` still
set — the `PAGE_FLAGS_CHECK_AT_FREE` `bad_page` the laptop dumped.  The concrete witness `⟨1, true⟩`
(one ref left, still LRU-flagged) put-to-0 is UNSAFE. -/
theorem put_while_flagged_unsafe : ¬ (Folio.put ⟨1, true⟩).SafeFree := by decide

/-- …and isolating that same state first makes it safe — the fix, on the same witness. -/
theorem isolate_fixes_it : ((Folio.isolate ⟨1, true⟩).put).SafeFree := by decide

/-- **The residual is ORTHOGONAL to the count fix**: even with perfectly balanced counts (`refs` reaches
0 legitimately, no phantom), the free is unsafe iff the flag was not cleared first.  So `GatherLedger`
(counts) and this (flags/ordering) are independent obligations — closing one does not close the other. -/
theorem flag_bug_independent_of_count (f : Folio) (hfreed : f.freed) (hfl : f.flagged = true) :
    ¬ f.SafeFree := by
  simp only [Folio.SafeFree, hfl]
  intro h; exact absurd (h hfreed) (by decide)

end LruIsolation
end Tessera

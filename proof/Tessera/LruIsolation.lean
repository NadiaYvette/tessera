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

/-! ## The boot-pinned site: the pgcl FLOOR frees an lru_add-pending folio past its batch ref

The reinc #36 boot pinned the concrete mechanism (12 bad_page → pcp free-list corruption → wedge).
`folios_put_refs`' pgcl refcount FLOOR drives a folio to 0 even when the per-cpu `lru_add` batch still
holds a reference — the folio is `PG_active` with `PG_lru` CLEAR (queued by `folio_add_lru`, not yet
drained onto the real LRU).  Freeing it there (a) reaches the buddy `PG_active`
(`PAGE_FLAGS_CHECK_AT_FREE` bad_page) and (b) leaves the batch a dangling pointer → when it drains it
corrupts the pcp free-list (`__rmqueue_pcplist` / `free_frozen_page_commit` list corruption) → the
allocator spins on `pcp->lock` → soft-lockup.  The defensive fix re-holds when `active ∧ ¬onLru`. -/

/-- LRU-lifecycle state.  `refs` refcount; `active` = PG_active; `onLru` = PG_lru.  A folio queued on the
per-cpu `lru_add` batch (not yet drained) is `active` with `onLru = false`, and the batch holds one ref. -/
structure LFolio where
  refs   : Nat
  active : Bool
  onLru  : Bool
deriving Repr, DecidableEq

/-- **PENDING on the lru_add batch** = PG_active set, PG_lru clear: queued but not drained.  Freeing here
dangles the batch pointer and reaches the buddy PG_active. -/
def LFolio.pending (f : LFolio) : Bool := f.active && !f.onLru

/-- The pgcl refcount FLOOR (`folios_put_refs`): drop `nr` refs, floored at 0 (never underflows). -/
def LFolio.floorPut (f : LFolio) (nr : Nat) : LFolio :=
  { f with refs := if f.refs > nr then f.refs - nr else 0 }

/-- The floor leaves `active`/`onLru` untouched — so it cannot fix a pending folio's flags. -/
theorem floorPut_pending (f : LFolio) (nr : Nat) : (f.floorPut nr).pending = f.pending := rfl

/-- **THE BUG — the bare floor frees a pending folio.**  With the batch's ref counted, `refs = m+1`; when
the gather over-drops (`nr ≥ refs`) the floor drives it to 0 while it is still `pending` — freed past the
batch ref (bad_page + dangling batch → pcp corruption). -/
theorem floor_frees_pending (f : LFolio) (nr : Nat) (hp : f.pending = true) (hover : f.refs ≤ nr) :
    (f.floorPut nr).refs = 0 ∧ (f.floorPut nr).pending = true := by
  refine ⟨?_, by rw [floorPut_pending]; exact hp⟩
  show (if f.refs > nr then f.refs - nr else 0) = 0
  rw [if_neg (by omega)]

/-- The FIX gate (the kernel's re-hold): if the folio is lru_add-`pending`, re-hold (keep it live);
otherwise apply the floor. -/
def LFolio.gatedPut (f : LFolio) (nr : Nat) : LFolio :=
  if f.pending = true then { f with refs := f.refs + 1 } else f.floorPut nr

/-- **THE FIX — the gate NEVER frees a pending folio.**  It re-holds, so `refs > 0`; the lru_add drain
later sets `onLru` and it is freed isolated (flags cleared).  Reincarnation of the wedge is impossible. -/
theorem gate_never_frees_pending (f : LFolio) (nr : Nat) (hp : f.pending = true) :
    0 < (f.gatedPut nr).refs := by
  show 0 < (if f.pending = true then { f with refs := f.refs + 1 } else f.floorPut nr).refs
  rw [if_pos hp]
  show 0 < f.refs + 1
  omega

/-- **…and the gate does NOT over-leak**: a genuinely dead, ISOLATED folio (`¬pending`) is still freed by
the floor as before — the gate only defers the unsafe (pending) frees. -/
theorem gate_frees_isolated (f : LFolio) (nr : Nat) (hnp : f.pending = false) (hover : f.refs ≤ nr) :
    (f.gatedPut nr).refs = 0 := by
  have hne : ¬ (f.pending = true) := by rw [hnp]; decide
  show (if f.pending = true then { f with refs := f.refs + 1 } else f.floorPut nr).refs = 0
  rw [if_neg hne]
  show (if f.refs > nr then f.refs - nr else 0) = 0
  rw [if_neg (by omega)]

/-- Concrete witness — the boot's case: a folio whose only ref is the lru_add batch's (`refs=1`), still
`active`, not yet `onLru`; the gather over-drops `nr=1`.  Bare floor frees it (bug); the gate holds it. -/
def lruPendingFolio : LFolio := ⟨1, true, false⟩

theorem witness_floor_frees : (lruPendingFolio.floorPut 1).refs = 0 ∧ lruPendingFolio.pending = true := by
  decide

theorem witness_gate_holds : 0 < (lruPendingFolio.gatedPut 1).refs := by decide

end LruIsolation
end Tessera

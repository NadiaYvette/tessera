/-
  Tessera — STALE-PUT / refcount-floor double-free (pgcl #143 task #20, the systemic residual).

  The reclaim/lru-drain audit (2026-07-03) found the second free the PGCL143-DOUBLEFREE detector
  reports (26x via folios_put_refs, 8x via shrink_folio_list, ...) is MANUFACTURED by the
  refcount FLOOR band-aid itself.  `folios_put_refs` (mm/swap.c) drops `k = nr_refs` from a
  cluster whose current refcount is `r`:

    * STOCK  `folio_ref_sub_and_test(folio, k)` frees iff the subtract lands EXACTLY on 0, i.e.
      r = k.  A stale/duplicate put against an already-free cluster (r = 0, k ≥ 1) subtracts to
      -1, returns false => NEVER frees.  (It underflows the refcount, but does not double-free.)

    * FLOOR  clamps `new = (r > k) ? r - k : 0` and frees iff `new = 0`, i.e. r ≤ k -- INCLUDING
      r = 0.  So a stale put on an ALREADY-FREE cluster frees it a SECOND time: the double-free.
      The floor, added to stop refcount UNDERFLOW, instead manufactures the DOUBLE-FREE.

    * GUARDED (the fix, `if (old == 0) continue;`) frees iff `0 < r ≤ k` -- reached 0 AND was
      live.  Matches stock's safety on stale puts, keeps the floor's clamp (no underflow), and
      still frees a genuine cross-mm over-put (0 < r < k) exactly once.

  This models all three free-decision policies and proves: the floor double-frees a stale put,
  stock and the fix do not, the fix changes behavior ONLY at r = 0 (zero blast radius), and the
  fix still frees the over-put the floor was designed for (which stock leaks).
-/
namespace Tessera
namespace StalePut

/-- STOCK `folio_ref_sub_and_test`: frees iff the drop lands exactly on 0 (r = k). -/
def stockFrees (r k : Nat) : Bool := decide (r = k)

/-- FLOOR band-aid (buggy): frees iff `max(0, r-k) = 0`, i.e. r ≤ k -- includes r = 0. -/
def floorFrees (r k : Nat) : Bool := decide (r ≤ k)

/-- GUARDED floor (the fix): frees iff it reached 0 AND was live: 0 < r ≤ k. -/
def guardedFrees (r k : Nat) : Bool := decide (0 < r ∧ r ≤ k)

/-- **THE BUG**: the floor frees a STALE put -- a drop against an already-free cluster (r = 0) --
for any k.  That second free is the PGCL143-DOUBLEFREE (freelist corruption / shared-page reuse
-> Electron int3 & segfault). -/
theorem floor_double_frees_stale (k : Nat) : floorFrees 0 k = true := by
  simp [floorFrees]

/-- **STOCK IS SAFE**: `sub_and_test` never frees a stale put (r = 0, real drop k ≥ 1) -- it
underflows to -1 and returns false. -/
theorem stock_no_free_stale (k : Nat) (hk : 1 ≤ k) : stockFrees 0 k = false := by
  simp only [stockFrees, decide_eq_false_iff_not]; omega

/-- **THE FIX IS SAFE**: the guarded floor never re-frees an already-free cluster -- no
double-free, for any k. -/
theorem guarded_no_free_stale (k : Nat) : guardedFrees 0 k = false := by
  simp [guardedFrees]

/-- **ZERO BLAST RADIUS**: on any LIVE cluster (r > 0) the guard is byte-identical to the floor;
the fix changes the free decision ONLY at r = 0. -/
theorem guarded_eq_floor_when_live (r k : Nat) (hr : 0 < r) :
    guardedFrees r k = floorFrees r k := by
  unfold guardedFrees floorFrees
  by_cases h : r ≤ k
  · simp [h, hr]
  · simp [h]

/-- **THE FIX PRESERVES THE OVER-PUT HANDLING**: a genuine cross-mm over-put (0 < r ≤ k, more
refs dropped than exist) is still freed exactly once -- the case the floor was designed for and
which STOCK gets wrong (underflows past 0 and never frees -> leak). -/
theorem guarded_frees_overput (r k : Nat) (hr : 0 < r) (hrk : r ≤ k) :
    guardedFrees r k = true := by
  simp [guardedFrees, hr, hrk]

/-- **THE FIX AGREES WITH STOCK ON THE NORMAL LAST PUT** (r = k ≥ 1): both free once. -/
theorem guarded_agrees_stock_exact (k : Nat) (hk : 1 ≤ k) :
    guardedFrees k k = true ∧ stockFrees k k = true := by
  refine ⟨?_, ?_⟩
  · simp [guardedFrees]; omega
  · simp [stockFrees]

/-! ### Concrete cases -/

/-- The stale put k=1 on an already-free cluster: FLOOR double-frees; stock and the fix do not. -/
theorem concrete_stale_put :
    floorFrees 0 1 = true ∧ stockFrees 0 1 = false ∧ guardedFrees 0 1 = false := by
  decide

/-- A cross-mm over-put r=2 k=5: the fix frees once (like the floor intended); STOCK leaks it. -/
theorem concrete_overput :
    guardedFrees 2 5 = true ∧ floorFrees 2 5 = true ∧ stockFrees 2 5 = false := by
  decide

end StalePut
end Tessera

/-
  Tessera — REFCOUNT CORRECTIVE FLOOR (r14reffloor, pgcl #143 task #8, the data-side face).

  r13refgate confirmed r12fix (mapcount corrective floor -> honest folio_mapcount) collapsed the
  code-page free-while-mapped (int3 91->28, Electron windows render).  The RESIDUAL is the same
  root -- the REFCOUNT over-drop (PGCL143-OVERPUT) at the gather discharge (folios_put_refs) -- now
  hitting the DATA side: anon env/argv pages freed WHILE STILL REFERENCED (the "environments not
  passed" ABI corruption) + the Bad rss MM_ANONPAGES+1 / MM_FILEPAGES-1 type-swap.

  r12fix fixed the count that LIES (mapcount); this fixes the count that FREES (refcount), SYMMETRIC:
  the current pgcl put floors the refcount at 0, which can drop it BELOW folio_mapcount = the refs
  the live mappings hold -> free-while-referenced.  Since r12fix makes folio_mapcount honest, it is
  a TRUSTWORTHY floor: never drop the refcount below it, so a referenced folio is never freed.
-/
namespace Tessera
namespace RefFloor

/- A put of `k` refs: refcount `rc`, honest mapping count `mc` (r12fix keeps mapcount >= present,
so `mc` is a trustworthy lower bound on the refs the live mappings hold). -/

/-- STOCK/current pgcl put: clamp at 0.  Can drop `rc` below `mc` -> free-while-referenced. -/
def putFloor0 (rc k : Nat) : Nat := if k ≤ rc then rc - k else 0

/-- r14 REFCOUNT CORRECTIVE FLOOR: never drop `rc` below `mc`.  A put that would over-drop the
mapping refs is clamped to `mc`, so a referenced folio keeps `rc >= mc >= 1` and is never freed. -/
def putFloorMc (rc mc k : Nat) : Nat := max (if k ≤ rc then rc - k else 0) mc

/-- **INVARIANT MAINTAINED**: the corrective put keeps `rc >= mc` -- refcount covers the mappings. -/
theorem putFloorMc_ge_mc (rc mc k : Nat) : mc ≤ putFloorMc rc mc k := by
  unfold putFloorMc
  by_cases hk : k ≤ rc
  · simp only [if_pos hk]; omega
  · simp only [if_neg hk]; omega

/-- **NO FREE WHILE MAPPED**: with the corrective floor `rc` reaches 0 ONLY when `mc = 0` (unmapped)
-- a referenced (mapped) folio is never freed. -/
theorem putFloorMc_free_only_unmapped (rc mc k : Nat) (h : putFloorMc rc mc k = 0) : mc = 0 := by
  have := putFloorMc_ge_mc rc mc k; omega

/-- **THE BUG (stock 0-floor)**: it CAN free a still-mapped folio -- a put `k >= rc` drives `rc` to
0 while `mc > 0` (the mapping refs over-dropped = the OVERPUT / env-page reuse). -/
theorem putFloor0_frees_mapped (rc k : Nat) (hk : rc ≤ k) : putFloor0 rc k = 0 := by
  unfold putFloor0
  by_cases h : k ≤ rc
  · simp only [if_pos h]; omega
  · simp only [if_neg h]

/-- **ZERO BLAST RADIUS**: when the put doesn't over-drop the mappings (sub-result >= mc) the
corrective floor equals the stock floor -- identical on every well-formed put. -/
theorem putFloorMc_eq_when_room (rc mc k : Nat)
    (h : mc ≤ (if k ≤ rc then rc - k else 0)) :
    putFloorMc rc mc k = (if k ≤ rc then rc - k else 0) := by
  unfold putFloorMc
  by_cases hk : k ≤ rc
  · simp only [if_pos hk] at h ⊢; omega
  · simp only [if_neg hk] at h ⊢; omega

/-! ### r16owefloor: also refuse to free a GATHER-OWED folio (the reincarnation face) -/

/-- r16: page_owner PROVED the residual double-free is a folio the mmu_gather still OWES,
over-dropped to 0 by a non-gather path while UNMAPPED (`mc = 0`, so `putFloorMc` lets it reach 0),
freed, reincarnated by `__vmalloc`, then stale-freed.  Extend the floor to also hold `>= 1` while
`owed` (and not the gather's own discharge): `floor = max(putFloorMc, if owed then 1 else 0)`. -/
def putFloorOwed (rc mc k : Nat) (owed : Bool) : Nat :=
  max (putFloorMc rc mc k) (if owed then 1 else 0)

/-- **THE r16 RESULT**: a gather-owed folio is NEVER freed by the over-drop (`refcount >= 1`), so it
cannot be freed-to-buddy while owed -> cannot be reincarnated by `__vmalloc` and stale-freed. -/
theorem putFloorOwed_owed_not_freed (rc mc k : Nat) : 1 ≤ putFloorOwed rc mc k true := by
  show 1 ≤ max (putFloorMc rc mc k) 1; omega

/-- **NO REINCARNATION**: an owed folio's refcount never reaches 0 -- the free-while-owed the
double-free needs is impossible. -/
theorem owed_never_freed (rc mc k : Nat) (h : putFloorOwed rc mc k true = 0) : False := by
  have := putFloorOwed_owed_not_freed rc mc k; omega

/-- **ZERO BLAST RADIUS**: not owed ⇒ identical to the r14 mapcount floor (the last put still
frees an unmapped, un-owed folio). -/
theorem putFloorOwed_eq_when_not_owed (rc mc k : Nat) :
    putFloorOwed rc mc k false = putFloorMc rc mc k := by
  show max (putFloorMc rc mc k) 0 = putFloorMc rc mc k; omega

/-- The owe floor never DROPS the mapcount floor (still `>= mc`), so it composes with r12fix/r14. -/
theorem putFloorOwed_ge_mc (rc mc k : Nat) (owed : Bool) : mc ≤ putFloorOwed rc mc k owed := by
  have h := putFloorMc_ge_mc rc mc k
  cases owed
  · show mc ≤ max (putFloorMc rc mc k) 0; omega
  · show mc ≤ max (putFloorMc rc mc k) 1; omega

/-! ### The full chain: both counts now floor at the present sub-PTEs -/

/-- **FULL CHAIN**: r12fix (`present ≤ mc`) + r14 (`mc ≤ rc`) ⇒ `present ≤ rc`, so a refcount-0 free
happens only when `present = 0` -- no sub-PTE maps it.  Both the count that lies (mapcount) and the
count that frees (refcount) floor at the present mappings; free-while-mapped is closed on BOTH. -/
theorem no_free_while_present (rc mc present : Nat)
    (h12 : present ≤ mc) (h14 : mc ≤ rc) (hfree : rc = 0) : present = 0 := by omega

/-- Concrete: a folio mapped by 3 sub-PTEs (mc=3, rc should be >=3), a bogus over-put of 5 refs.
Stock floor frees it (0, while mapped); the corrective floor holds it at 3. -/
theorem concrete :
    putFloor0 3 5 = 0 ∧ putFloorMc 3 3 5 = 3 := by decide

end RefFloor
end Tessera

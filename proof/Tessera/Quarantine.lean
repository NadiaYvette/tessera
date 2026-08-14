/-
  Tessera — REINCARNATION QUARANTINE at the universal free chokepoint (pgcl #143 task #20).

  The r6floor laptop boot showed the residual double-free is a REINCARNATION: a pfn a mmu_gather
  still OWES a deferred put for is freed by a concurrent path (a floored over-put drove the
  aggregate refcount to 0), reaches the buddy freelist, is re-handed-out to a new owner, and the
  owing gather's later discharge frees it again -> corruption (44x 2nd-freed by vfree during
  module load; int3 in shared libcef.so; rss FILE<->ANON type-swap).

  The existing REINCARN-GATE (mm/page_alloc.c free_unref_folios) refuses such a free -- but ONLY
  on the folio-batch path.  vfree / tlb_remove_table_rcu / make_alloc_exact / rcu_do_batch reach
  the buddy through __free_pages_prepare WITHOUT that gate, so an owed pfn freed via those paths
  still reincarnates.  THE FIX: put the guard at __free_pages_prepare -- the UNIVERSAL chokepoint
  every free funnels through -- so an owed pfn is refused on EVERY path.

  This models the invariant and proves WHY universal coverage (not per-path) is what closes it:
  an owed pfn must never become reusable until the owing gather discharges.
-/
namespace Tessera
namespace Quarantine

/-- An abstract free path (folio-batch, vfree, page-table RCU, alloc_exact, ...). -/
abbrev Path := Nat

/-- pfn state across the deferred-free window.  `owed` = a mmu_gather still owes a deferred put;
`reusable` = the pfn is on the buddy freelist and can be handed to a NEW owner (= reincarnation
if it is still owed). -/
structure St where
  owed : Bool
  reusable : Bool
deriving Repr, DecidableEq

/-- A premature free of the pfn via a path that is (`gated=true`) or is not (`gated=false`)
covered by the reincarnation guard.  Gated: refuse -- leave the pfn off the freelist, owe kept
(the owing gather's discharge frees it later).  Ungated: the pfn reaches the freelist while still
owed -> reusable-while-owed = reincarnation. -/
def freeVia (gated : Bool) (s : St) : St :=
  if s.owed && !gated then { s with reusable := true } else s

/-- The owing gather's own discharge: clears the owe and frees the pfn exactly once (legitimate). -/
def discharge (_s : St) : St := { owed := false, reusable := true }

/-- **THE FIX (per pfn)**: a gated free never makes an owed pfn reusable -- no reincarnation. -/
theorem gated_not_reusable (s : St) (h : s.owed = true) (hr : s.reusable = false) :
    (freeVia true s).reusable = false := by
  simp [freeVia, h, hr]

/-- **THE BUG (per pfn)**: an ungated free makes an owed pfn reusable -> reincarnation. -/
theorem ungated_reincarnates (s : St) (h : s.owed = true) :
    (freeVia false s).reusable = true := by
  simp [freeVia, h]

/-- **NO LEAK**: the owing gather's discharge does free the pfn (reusable), with the owe cleared
-- so it is freed exactly once, legitimately, not held forever. -/
theorem discharge_frees (s : St) :
    (discharge s).reusable = true ∧ (discharge s).owed = false := by
  simp [discharge]

/-! ### Coverage: the guard must sit at the UNIVERSAL chokepoint, not per-path -/

/-- The guard's coverage over free paths. -/
def Coverage := Path → Bool

/-- Universal coverage = __free_pages_prepare (every free path funnels through it). -/
def universal : Coverage := fun _ => true

/-- Partial coverage = the old free_unref_folios-only gate: only the folio-batch path is gated. -/
def onlyFolioBatch (fb : Path) : Coverage := fun p => decide (p = fb)

/-- **THE FIX (coverage)**: under universal coverage, an owed pfn freed via ANY path stays
non-reusable -- reincarnation is impossible on every path. -/
theorem universal_safe (s : St) (p : Path) (h : s.owed = true) (hr : s.reusable = false) :
    (freeVia (universal p) s).reusable = false := by
  simp only [universal]; exact gated_not_reusable s h hr

/-- **THE BUG (coverage)**: under partial coverage, an owed pfn freed via any OTHER path
(vfree / page-table RCU / alloc_exact) reincarnates -- the r6floor 44x-vfree leak. -/
theorem partial_leaks_offpath (s : St) (fb p : Path) (hp : p ≠ fb) (h : s.owed = true) :
    (freeVia (onlyFolioBatch fb p) s).reusable = true := by
  have hcov : onlyFolioBatch fb p = false := by
    simp only [onlyFolioBatch, decide_eq_false_iff_not]; exact hp
  rw [hcov]; exact ungated_reincarnates s h

/-- The partial gate DID cover its own path (folios_put_refs caught the folio-batch frees) -- so
the residual leak is exactly the OFF-path frees, which universal coverage closes. -/
theorem partial_covers_onpath (s : St) (fb : Path) (h : s.owed = true) (hr : s.reusable = false) :
    (freeVia (onlyFolioBatch fb fb) s).reusable = false := by
  have hcov : onlyFolioBatch fb fb = true := by simp [onlyFolioBatch]
  rw [hcov]; exact gated_not_reusable s h hr

/-! ### Concrete: an owed pfn, freed off-path -/

/-- An owed, not-yet-reusable pfn. -/
def owedPfn : St := { owed := true, reusable := false }

/-- Off-path free (ungated) reincarnates it; the universal gate does not; discharge frees it. -/
theorem concrete :
    (freeVia false owedPfn).reusable = true ∧
    (freeVia true owedPfn).reusable = false ∧
    (discharge owedPfn).reusable = true := by
  decide

end Quarantine
end Tessera

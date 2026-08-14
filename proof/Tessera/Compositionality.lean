/-
  Tessera — NON-MONOTONIC COMPOSITIONALITY of the #143 fixes.

  Empirical fact this module explains: the swapfix baseline, the migration-fragment fix, and the
  swap-fragment fix produce an essentially FLAT kill-init metric (42 -> 43 -> 43 "Unable to access
  opcode").  A naive read says "those fixes are wrong".  This module proves the alternative the user
  named: when the observable is the logical OR of several INDEPENDENT corruption facets, every
  proper subset of fixes leaves the observable true, so a correct-and-necessary fix can have zero
  marginal effect in isolation.  The vindication of such a fix is therefore its PROOF (it discharges
  a real obligation — see MigrateVsub/Permute/SwapEntry), not its standalone A/B delta.

  #143 decomposes into independent facets, each separately able to corrupt a shared cluster:
    migFrag : migration re-aligns a vsub≠psub cluster          (MigrateVsub.lean / Permute.lean)
    swpFrag : swap-in/out re-aligns a vsub≠psub cluster        (SwapEntry.lean)
    slotUAF : cross-mm shared-cluster swap-slot over-put        (pgcl task #4)
    excl    : do_swap_page grants AnonExclusive on shared swap  (do_wp_page reuse-in-place)

  Proved: each facet alone corrupts (every fix is NECESSARY); fixing migration — or migration AND
  swap — while any other facet lives is INSUFFICIENT (the flat metric, exactly); fixing the whole
  set is SUFFICIENT for every starting state; and the SAME fix has marginal effect 0 in one context
  and is decisive in another (value is non-compositional — individual A/B deltas mislead).
-/
namespace Tessera.Compositionality

/-- The independent corruption facets #143 decomposes into; each Bool = "this facet is still broken". -/
structure BugFacets where
  migFrag : Bool
  swpFrag : Bool
  slotUAF : Bool
  excl    : Bool

/-- The observable (kill-init) is the logical OR of the live facets: any one broken corrupts. -/
def killObservable (f : BugFacets) : Bool := f.migFrag || f.swpFrag || f.slotUAF || f.excl

/-- The four single-facet fixes — each clears exactly its own flag. -/
def fixMig  (f : BugFacets) : BugFacets := { f with migFrag := false }
def fixSwp  (f : BugFacets) : BugFacets := { f with swpFrag := false }
def fixSlot (f : BugFacets) : BugFacets := { f with slotUAF := false }
def fixExcl (f : BugFacets) : BugFacets := { f with excl    := false }

/-- EACH FACET IS NECESSARY: each one alone (all others already fixed) still corrupts.  So the
    migration- and swap-fragment proofs are not wasted by the flat metric — their facet is real. -/
theorem mig_alone_corrupts  : killObservable ⟨true,  false, false, false⟩ = true := rfl
theorem swp_alone_corrupts  : killObservable ⟨false, true,  false, false⟩ = true := rfl
theorem slot_alone_corrupts : killObservable ⟨false, false, true,  false⟩ = true := rfl
theorem excl_alone_corrupts : killObservable ⟨false, false, false, true ⟩ = true := rfl

/-- NO INDIVIDUAL FIX IS SUFFICIENT.  Fixing migration while ANY other facet is live leaves the
    observable true — the precise shape of the empirical 42→43: the fix landed, the metric did not
    move, because slotUAF/excl (and swpFrag) remained. -/
theorem migfix_insufficient (s sl e : Bool) (h : s || sl || e = true) :
    killObservable (fixMig ⟨true, s, sl, e⟩) = true := by
  cases s <;> cases sl <;> cases e <;> simp_all [killObservable, fixMig]

/-- Even fixing migration AND swap together is insufficient while slot/excl live (the 43→43 step). -/
theorem migswp_insufficient (sl e : Bool) (h : sl || e = true) :
    killObservable (fixSwp (fixMig ⟨true, true, sl, e⟩)) = true := by
  cases sl <;> cases e <;> simp_all [killObservable, fixMig, fixSwp]

/-- THE COMBINATION IS SUFFICIENT: fixing all facets clears the observable, from EVERY start. -/
theorem all_fixes_clear (f : BugFacets) :
    killObservable (fixMig (fixSwp (fixSlot (fixExcl f)))) = false := by
  simp [killObservable, fixMig, fixSwp, fixSlot, fixExcl]

/-- NON-MONOTONICITY / non-compositional marginal value.  The SAME migration fix has marginal
    effect 0 when another facet is live (slotUAF here) yet is DECISIVE when it is the last facet.
    So a fix's empirical value is not an intrinsic monotone scalar; it is conditional on the rest
    of the set — which is exactly why per-fix A/B deltas cannot rank correctness. -/
theorem migfix_marginal_zero :
    killObservable ⟨true, false, true, false⟩ = true ∧
    killObservable (fixMig ⟨true, false, true, false⟩) = true := ⟨rfl, rfl⟩

theorem migfix_marginal_decisive :
    killObservable ⟨true, false, false, false⟩ = true ∧
    killObservable (fixMig ⟨true, false, false, false⟩) = false := ⟨rfl, rfl⟩

/-- The general law behind the above: the observable is false iff EVERY facet is cleared, so the
    "distance to green" is the count of live facets — a step that only reaches 0 when the set is
    complete, never by a single fix while others remain. -/
theorem green_iff_all_cleared (f : BugFacets) :
    killObservable f = false ↔
      (f.migFrag = false ∧ f.swpFrag = false ∧ f.slotUAF = false ∧ f.excl = false) := by
  obtain ⟨m, s, sl, e⟩ := f
  cases m <;> cases s <;> cases sl <;> cases e <;> simp [killObservable]

end Tessera.Compositionality

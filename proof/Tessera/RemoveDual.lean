/-
  Tessera — the REMOVE-SIDE DUAL of SingleRoot, and the per-cluster rmap fix (pgcl #143 R15/R16/R17).

  The disc4 boot refuted the install-side root (`nr < k`): every install path is statically balanced
  (`add == set == nr`). The over-remove is a path-agnostic **cluster-level rmap double-DISCHARGE** — the
  cluster's single `_mapcount` is driven ~2× below where the present sub-PTEs justify, yet every unmap op
  removes exactly the sub-PTEs it clears. R15's insight: a remove-side double-discharge fits
  `dual_lockstep` *identically* to an install under-add — `SingleRoot` is the install-side dual, this is
  its remove-side mirror, and the lockstep alone cannot tell them apart (only the install-balance check /
  the boot can). This file proves that indistinguishability, then formalizes R17's structural diagnosis
  and fix: a per-cluster `_mapcount` maintained by independent per-sub-PTE ±1 (with `pte_pfn` head-page
  aliasing) is FRAGILE — a spurious `-1` (a remove not backed by a present→absent transition, invisible
  to the aliased counter) drifts it; the per-cluster "first-in / last-out" discipline (mainline
  `_nr_pages_mapped` style) makes `_mapcount` a FUNCTION of the present-set, hence idempotent to the
  double-discharge.
-/
import Tessera.SingleRoot

namespace Tessera

/-! ### The remove-side dual — indistinguishable from the install under-add by the lockstep. -/

/-- Install is BALANCED (`added = present = k`), but the teardown discharges `r` rmap removes (and `r`
matching ref drops). A double-discharge is `r > k` — some sub-PTE removed twice. -/
def removeCycle (base k r : Int) : DualCount := ((DualCount.fresh base).install k k).zap r

/-- The remove-side double-discharge drives BOTH ledgers down by the over-count `d = r − k`, in lockstep
— the same `refcount:−d mapcount:−d` signature as the install under-add. -/
theorem remove_dual_lockstep (base k r : Int) :
    (removeCycle base k k).rmap - (removeCycle base k r).rmap = r - k
    ∧ (removeCycle base k k).ref - (removeCycle base k r).ref = r - k := by
  simp only [removeCycle, DualCount.fresh, DualCount.install, DualCount.zap]
  refine ⟨by omega, by omega⟩

/-- **THE INDISTINGUISHABILITY (R15, proved).** An install under-add by `d` (`cycle base (k−d) k`) and a
remove over-discharge by `d` (`removeCycle base k (k+d)`) leave the SAME `(rmap, ref) = (−d, base−d)`.
`dual_lockstep` cannot separate the two roots; only the install-balance check (R15) or the discriminator
boot can — which is exactly why the boot was necessary, and why it could overturn the install-side root
without overturning the lockstep. -/
theorem install_remove_indistinguishable (base k d : Int) :
    (cycle base (k - d) k).rmap = (removeCycle base k (k + d)).rmap
    ∧ (cycle base (k - d) k).ref = (removeCycle base k (k + d)).ref := by
  have h1 := cycle_rmap base (k - d) k
  have h2 := cycle_ref base (k - d) k
  simp only [removeCycle, DualCount.fresh, DualCount.install, DualCount.zap]
  refine ⟨by omega, by omega⟩

/-! ### The structural diagnosis and fix — per-sub-PTE (fragile) vs per-cluster (robust). -/

/-- A cluster's rmap state: `present` = the true count of present sub-PTEs; `mc` = the single
(head-page-aliased) `_mapcount`. Faithful means `mc` reads the present-set correctly. -/
structure ClusterRmap where
  present : Nat
  mc      : Int
deriving Repr

/-- Per-cluster faithful reading: `_mapcount` reflects whether the cluster is mapped at all (mainline
`_nr_pages_mapped` semantics — kernel-pages-mapped, not hardware-PTEs). -/
def ClusterRmap.faithful (c : ClusterRmap) : Prop := c.mc = (if c.present = 0 then (0 : Int) else 1)

/-- A SPURIOUS remove — a `-1` with NO real present→absent transition (the double-discharge: the aliased
counter cannot see that this sub-PTE was already absent). Under the PER-SUB-PTE scheme it still
decrements. -/
def perSub_spurious (c : ClusterRmap) : ClusterRmap := { c with mc := c.mc - 1 }

/-- The PER-CLUSTER scheme recomputes `mc` from the (unchanged) present-set. -/
def perClus_spurious (c : ClusterRmap) : ClusterRmap := { c with mc := if c.present = 0 then 0 else 1 }

/-- **THE BUG.** A spurious per-sub-PTE remove drifts `mc` one below its faithful value — the
double-discharge underflow, invisible to the aliased counter (present unchanged, `mc` dropped). -/
theorem perSub_spurious_drifts (c : ClusterRmap) : (perSub_spurious c).mc = c.mc - 1 := rfl

theorem perSub_breaks_faithful (c : ClusterRmap) (hf : c.faithful) (h : 0 < c.present) :
    ¬ (perSub_spurious c).faithful := by
  simp only [ClusterRmap.faithful, perSub_spurious] at *
  rw [if_neg (show ¬ c.present = 0 by omega)] at hf ⊢
  omega

/-- **THE FIX.** A spurious per-cluster remove is a NO-OP on the counter (recomputed from the unchanged
present-set) — idempotent, so a double-discharge cannot underflow it. -/
theorem perClus_spurious_noop (c : ClusterRmap) (h : 0 < c.present) : (perClus_spurious c).mc = 1 := by
  simp only [perClus_spurious]; rw [if_neg (show ¬ c.present = 0 by omega)]

/-- …and more: the per-cluster reading is faithful BY CONSTRUCTION after any (even spurious) remove —
`mc` is a function of the present-set, so no sequence of mis-counted removes can break the invariant. This
is precisely why "count rmap per cluster (kernel page), not per sub-PTE" is a root fix, not a band-aid. -/
theorem perClus_preserves_faithful (c : ClusterRmap) : (perClus_spurious c).faithful := by
  simp only [ClusterRmap.faithful, perClus_spurious]

end Tessera

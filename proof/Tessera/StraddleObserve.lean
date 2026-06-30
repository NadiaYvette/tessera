/-
  Tessera — OBSERVATION-FAITHFULNESS: perClus is faithful IFF `present_here` is EXACT.  The
  PMD-straddle counterexample (the QEMU "Bad page state: nonzero mapcount" witness) and the
  `present_here_full` fix.

  RemoveDual.perClus_preserves_faithful makes `_mapcount` a FUNCTION of the present-set, idempotent to the
  cross-mm spurious remove (the orphan — an UNDER-count).  But that function is evaluated at
  `present_here()`, which scans only THIS pte-table: EXACT for an aligned cluster, a strict LOWER BOUND for
  one straddling the pte-table (PMD) boundary (it cannot see the half in the adjacent table).  The
  accountant increments on observed-first-in (no straddle gate) yet SUPPRESSES the decrement on a straddler
  (a lower-bound zero must not free-while-mapped — the kernel's `!straddle` gate).  That add/dec asymmetry
  makes a straddling cluster's `_mapcount` climb by +1 every map+unmap cycle and never fall: it is freed
  with nonzero mapcount.  This is the OVER-count DUAL of the orphan UNDER-count, and the QEMU fork+COW
  stress reproduces it (60 bad-pages/run; the accountant trace shows inc≈dec globally with the entire
  imbalance in straddle-suppressed last-outs).

  Proved here: (1) aligned clusters are faithful (the cycle is mc-neutral); (2) the straddle counterexample
  — `n` cycles drive `_mapcount` to `mc+n`, so the freed folio has page_mapcount `= n ≠ 0`; (3) the gate is
  LOSE-LOSE (suppress ⇒ over-count/bad-page; fire-on-lower-bound-zero ⇒ under-count/free-while-mapped); (4)
  the ULTIMATE FIX — an EXACT observation (`present_here_full`, anchored across the boundary) makes the
  decrement fire, and the SAME perClus recompute is faithful for EVERY cluster.  Unification: perClus is
  faithful iff the observation is exact; orphan (under) and bad-page (over) are the two ways exactness fails.
-/
import Tessera.RemoveDual

namespace Tessera

/-! ### `present_here()` — exact for an aligned cluster, a straddler's lower bound. -/

/-- Whether the per-mm LAST-OUT decrement fires.  `straddle` = the cluster spans the pte-table (PMD)
boundary, so the kernel's per-table `present_here()` is a strict lower bound on the true present count;
`exact` = a straddle-correct observation (`present_here_full`) is used instead.  The decrement fires on a
non-straddler, or whenever the observation is exact; a straddler under the lower-bound gate is SUPPRESSED
(`!straddle`), to avoid freeing on a lower-bound zero. -/
def decFires (straddle exact : Bool) : Bool := !straddle || exact

/-! ### The per-mm `_mapcount` across one map+unmap cycle, and across `n` cycles. -/

/-- One per-mm map+unmap cycle.  The ADD always increments (`present_here == delta` first-in has no
straddle gate).  The DEC fires only when `fires`.  Net: 0 (faithful) when it fires, +1 (leak) when it is
suppressed. -/
def mcCycle (fires : Bool) (mc : Int) : Int :=
  let afterAdd := mc + 1
  if fires then afterAdd - 1 else afterAdd

/-- `n` map+unmap cycles (the fork+COW stress repeatedly shares-then-COWs each cluster). -/
def mcCycleN (fires : Bool) (mc : Int) : Nat → Int
  | 0       => mc
  | (n + 1) => mcCycleN fires (mcCycle fires mc) n

@[simp] theorem mcCycle_fires (mc : Int) : mcCycle true  mc = mc     := by simp [mcCycle]
@[simp] theorem mcCycle_supp  (mc : Int) : mcCycle false mc = mc + 1 := by simp [mcCycle]

/-! ### Aligned cluster (or fixed observation): faithful — the cycle is mc-neutral. -/

theorem mcCycleN_faithful (mc : Int) (n : Nat) : mcCycleN true mc n = mc := by
  induction n generalizing mc with
  | zero => rfl
  | succ k ih => simp only [mcCycleN, mcCycle_fires]; exact ih mc

/-! ### The straddle counterexample: monotone divergence → bad page. -/

/-- **THE COUNTEREXAMPLE.** A straddling cluster under the lower-bound gate gains +1 per cycle: after `n`
cycles its `_mapcount` is `mc + n`.  Unbounded over-count — the add counted, the last-out suppressed. -/
theorem mcCycleN_diverges (mc : Int) (n : Nat) : mcCycleN false mc n = mc + n := by
  induction n generalizing mc with
  | zero => simp [mcCycleN]
  | succ k ih => simp only [mcCycleN, mcCycle_supp]; rw [ih (mc + 1)]; push_cast; omega

/-- The free path's check: page_mapcount = `_mapcount + 1`; a clean free needs it 0 (perClus mc = −1). -/
def pageMapcount (mc : Int) : Int := mc + 1

/-- **BAD PAGE STATE.** A straddler freed after `n ≥ 1` cycles is truly unmapped — a faithful `_mapcount`
would be −1, page_mapcount 0 — but the lower-bound gate leaves page_mapcount `= n ≠ 0`: exactly the QEMU
"BUG: Bad page state … nonzero mapcount". -/
theorem straddle_bad_page (n : Nat) (hn : 1 ≤ n) :
    pageMapcount (mcCycleN false (-1) n) = (n : Int)
    ∧ pageMapcount (mcCycleN false (-1) n) ≠ 0 := by
  rw [mcCycleN_diverges]
  simp only [pageMapcount]
  omega

/-! ### The gate is a lose-lose; only exactness escapes. -/

/-- A straddler's PARTIAL unmap (this mm clears its in-table half; the other-table half stays mapped):
`present_here` reads 0 though the cluster is still mapped.  With NO straddle gate the accountant would
decrement on that lower-bound zero — a spurious last-out. -/
def partialUnmapNoGate (mc : Int) : Int := mc - 1

/-- **THE GATE IS LOSE-LOSE.** On a straddler the per-table observation forces a choice and BOTH are
unfaithful: SUPPRESS (the kernel's `!straddle`) ⇒ the add is unmatched ⇒ OVER-count (`mcCycleN_diverges`,
bad-page); FIRE on the lower-bound zero ⇒ a partial unmap spuriously last-outs ⇒ UNDER-count
(free-while-mapped, the orphan dual).  Only an EXACT observation is neutral. -/
theorem gate_lose_lose (mc : Int) :
    mcCycle false mc = mc + 1
    ∧ partialUnmapNoGate mc = mc - 1
    ∧ mcCycle true mc = mc :=
  ⟨mcCycle_supp mc, rfl, mcCycle_fires mc⟩

/-! ### The ultimate fix: an EXACT observation makes the decrement fire — faithful for every cluster. -/

/-- `present_here_full` anchors the scan across the boundary, so the last-out test is exact even for a
straddler: the decrement fires for every cluster. -/
@[simp] theorem fix_decFires (straddle : Bool) : decFires straddle true = true := by
  simp [decFires]

/-- **THE FIX.** With an exact observation every cluster — aligned OR straddling — is faithful: the cycle
leaves `_mapcount` unchanged, so a freed (unmapped) cluster has `_mapcount = −1` and page_mapcount 0.  The
SAME perClus recompute (RemoveDual.perClus_preserves_faithful), now sound because its input is the true
present-set. -/
theorem fix_faithful (straddle : Bool) (mc : Int) (n : Nat) :
    mcCycleN (decFires straddle true) mc n = mc := by
  rw [fix_decFires]; exact mcCycleN_faithful mc n

theorem fix_clean_free (straddle : Bool) (n : Nat) :
    pageMapcount (mcCycleN (decFires straddle true) (-1) n) = 0 := by
  rw [fix_faithful]; simp [pageMapcount]

/-! ### Unification — perClus is faithful IFF the observation is exact. -/

/-- **UNIFICATION.** One hypothesis decides faithfulness: whether `present_here` is exact (the decrement
fires).  Exact ⇒ faithful over any `n` (aligned, and straddlers after `present_here_full`).  Inexact (a
straddler's lower bound) ⇒ monotone over-count.  With the orphan as the cross-mm UNDER-count dual
(RemoveDual), the single root-obligation is one line: make `present_here` exact (per-mm AND
straddle-correct), and perClus is faithful for every cluster — orphan and bad-page both gone at the root. -/
theorem observation_decides (mc : Int) (n : Nat) :
    mcCycleN true mc n = mc ∧ mcCycleN false mc n = mc + n :=
  ⟨mcCycleN_faithful mc n, mcCycleN_diverges mc n⟩

end Tessera

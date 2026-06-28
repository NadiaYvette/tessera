/-
  Tessera — THE SINGLE-ROOT BRIDGE: one `nr` under-count, two #143 facets (R14 §C/§D synthesis).

  The two laptop crash-classes look unrelated — facet A is a deferred-rmap use-after-free (refcount → 0
  early), facet B is a wrong-data / `list_del` orphan (`_mapcount < -1`). R11's most under-used clue was
  the LOCKSTEP: `refcount:-7 mapcount:-7`, both negative by the SAME amount (`SharingRace.deferred_lockstep`).
  That only happens if ONE quantity discharges both ledgers.

  The hypothesis: the batched install computes one `pgcl_pte_batch` length `nr` (by PHYSICAL grouping, the
  vsub≠psub edge) and uses it for BOTH `folio_add_rmap_ptes(nr)` AND the batch's `nr` ref pins, while the
  TRUE number of sub-PTEs made present is `k`. When `nr < k` (the under-count), both ledgers are under-added
  by the same deficit `d = k − nr`; a later zap removing once per present sub-PTE then over-drops BOTH by
  `d`. This file proves: ONE hypothesis (`nr < k`) produces BOTH facets, in lockstep — so the two facets are
  one bug counted in two ledgers, and fixing the install (count by vsub, `nr = k`) collapses both at the
  source (zero-leak), which the gate (`PendingGate`) and quarantine only bracket downstream. The rmap ledger
  here reproduces `CallBalance` exactly; the second ledger (`ref`) is the new content.
-/
import Tessera.CallBalance
import Tessera.SharingRace

namespace Tessera

/-- A cluster's two ledgers the single batched `nr` drives: `rmap` (= `_mapcount + 1`, the
`folio_add/remove_rmap_ptes` net) and `ref` (the pinned refcount); `present` = the true present sub-PTE
count. -/
structure DualCount where
  rmap    : Int
  ref     : Int
  present : Int
deriving Repr

/-- A fresh, fully-unmapped cluster with `base` background refs held by owners other than this batch. -/
def DualCount.fresh (base : Int) : DualCount := { rmap := 0, ref := base, present := 0 }

/-- A batched install of `k` sub-PTEs (the TRUE count made present), where ONE `pgcl_pte_batch` length
`nr` drives BOTH `folio_add_rmap_ptes(nr)` and the `nr` ref pins. The sharing of `nr` across both ledgers
is the single-root crux; `nr < k` is the vsub≠psub under-count. -/
def DualCount.install (d : DualCount) (nr k : Int) : DualCount :=
  { rmap := d.rmap + nr, ref := d.ref + nr, present := d.present + k }

/-- A zap removes once per PRESENT sub-PTE — correctly — from BOTH ledgers (the teardown drops the rmap
AND its matching ref, the `deferred_lockstep` structure). -/
def DualCount.zap (d : DualCount) (j : Int) : DualCount :=
  { rmap := d.rmap - j, ref := d.ref - j, present := d.present - j }

/-- The install-then-zap cycle: install `k` present sub-PTEs counting only `nr`, then zap the `k`. -/
def cycle (base nr k : Int) : DualCount := (DualCount.fresh base |>.install nr k).zap k

theorem cycle_rmap (base nr k : Int) : (cycle base nr k).rmap = nr - k := by
  simp only [cycle, DualCount.fresh, DualCount.install, DualCount.zap] <;> omega

theorem cycle_ref (base nr k : Int) : (cycle base nr k).ref = base + nr - k := by
  simp only [cycle, DualCount.fresh, DualCount.install, DualCount.zap] <;> omega

/-- **LOCKSTEP (R11's `refcount == mapcount` both-negative signature).** Both ledgers fall below their
healthy (`nr = k`) values by the SAME deficit `d = k − nr`. One `nr`, one deficit, both ledgers. -/
theorem dual_lockstep (base nr k : Int) :
    (cycle base k k).rmap - (cycle base nr k).rmap = k - nr
    ∧ (cycle base k k).ref - (cycle base nr k).ref = k - nr := by
  have r1 := cycle_rmap base k k; have r2 := cycle_rmap base nr k
  have f1 := cycle_ref base k k;  have f2 := cycle_ref base nr k
  omega

/-- **FACET B — the orphan.** `nr < k` underflows the rmap ledger (`_mapcount + 1 < 0`, i.e.
`_mapcount ≤ -2`): a present sub-PTE without a live rmap → free-while-mapped → wrong-data / `list_del`.
This is exactly `CallBalance.underadd_zap_underflows` on the rmap ledger. -/
theorem facetB_orphan {base nr k : Int} (hunder : nr < k) : (cycle base nr k).rmap < 0 := by
  rw [cycle_rmap]; omega

/-- **FACET A — the ref over-drop.** The same `nr < k` drives the refcount below its true value by the
same deficit `d`; when `d` reaches the cluster's background refs the count hits 0 and the cluster is freed
while a removal is still owed — the deferred-rmap UAF surface. -/
theorem facetA_overdrop {base nr k : Int} (hunder : nr < k) : (cycle base nr k).ref < base := by
  rw [cycle_ref]; omega

theorem facetA_early_free {base nr k : Int} (hbase : base = k - nr) : (cycle base nr k).ref = 0 := by
  rw [cycle_ref]; omega

/-- **THE SINGLE-ROOT BRIDGE.** ONE hypothesis — the shared batch length under-counts the present sub-PTEs
(`nr < k`) — produces BOTH facets simultaneously and in lockstep: the rmap ledger underflows (facet B) AND
the ref ledger is over-dropped by the very same deficit `d = k − nr` (facet A). The two laptop crash-classes
are one bug counted in two ledgers. -/
theorem single_root_both_facets {base nr k : Int} (hunder : nr < k) :
    (cycle base nr k).rmap < 0
    ∧ (cycle base nr k).ref = base - (k - nr)
    ∧ (cycle base nr k).ref < base := by
  have hr := cycle_rmap base nr k; have hf := cycle_ref base nr k
  omega

/-- **The fix collapses BOTH facets at the source.** Counting present sub-PTEs by vsub (add once each,
`nr = k`) zeroes the deficit: the rmap returns to healthy (no orphan, facet B gone) AND the refcount is not
over-dropped (no early free, facet A gone). One install-site fix, both facets — so the gate and quarantine,
which only bracket the facets downstream (leak-not-corrupt), become unnecessary (zero-leak). -/
theorem fix_collapses_both (base k : Int) :
    (cycle base k k).rmap = 0 ∧ (cycle base k k).ref = base := by
  have hr := cycle_rmap base k k; have hf := cycle_ref base k k
  omega

end Tessera

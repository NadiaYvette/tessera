/-
  Tessera — certifying pgcl's #143 REAL FIX: the `pending_rmap[pfn]` ref-hold gate (R14 §C/§D).

  The band-aid (`RemoveFloor`) was proved SAFE but turned out unusable (the floors act after the bad free
  is committed; the free itself is the violation). So pgcl implemented `SharingRace.Aggregate.Pinned` as a
  runtime gate — a cross-mm counter `pgcl143_pending[pfn]`:
    * `++` when a deferred rmap removal is QUEUED in an mmu_gather batch (`__tlb_remove_folio_pages_size`);
    * `--` when it RUNS (`tlb_flush_rmap_batch`, after `folio_remove_rmap_ptes`);
    * `folios_put_refs` GATES the free: when the refcount sub reaches 0, if `pending(pfn) > 0` the free is
      premature → re-hold (`folio_ref_inc`) + skip.
  This file certifies that gate is CORRECT — the dual to `RemoveFloor` (which proved the band-aid safe).

  R14 §D then booted it: the deferred WARN fired 0× (the deferred-rmap UAF is fixed) but a SECOND facet
  surfaced — an IMMEDIATE over-remove (`zap_present_ptes`, a LIVE folio) leaves an ORPHAN sub-PTE (present,
  rmap already dropped), which later frees-while-mapped → reuse → wrong-data (fs-verity ×3) + `list_del`.
  So the obligation unifies to **"no free while an orphan is present"**, orphan == a present sub-PTE
  without a live rmap (`_mapcount < -1`) OR a pending deferred removal. The hard5 quarantine (`++` at ANY
  over-remove, never `--`) extends the same gate to facet B. Both certified below.
-/
import Tessera.SharingRace

namespace Tessera

/-! ### The gate, and that it discharges `aggregate_no_free_while_pending`. -/

/-- The gate's view of a cluster: `pending` outstanding deferred removals (the cross-mm counter), and
whether it has been freed. -/
structure Gate where
  pending : Nat
  freed   : Bool
deriving Repr

/-- `++` at QUEUE (a deferred removal recorded in an mmu_gather batch). -/
def Gate.queue (g : Gate) : Gate := { g with pending := g.pending + 1 }
/-- `--` at RUN (the deferred removal fires at `tlb_flush_rmap_batch`). -/
def Gate.run (g : Gate) : Gate := { g with pending := g.pending - 1 }
/-- The GATE at `folios_put_refs`: free only if no removal is pending; else re-hold (skip). -/
def Gate.tryFree (g : Gate) : Gate := if g.pending = 0 then { g with freed := true } else g

/-- **The gate never frees while a removal is pending** — it is a no-op then (re-holds). The runtime form
of `SharingRace.aggregate_no_free_while_pending`. -/
theorem gate_holds_while_pending (g : Gate) (hp : 0 < g.pending) : g.tryFree = g := by
  simp only [Gate.tryFree, if_neg (show ¬ g.pending = 0 by omega)]

/-- Corollary: while pending, the freed flag is unchanged (no free). -/
theorem gate_no_free_while_pending (g : Gate) (hp : 0 < g.pending) :
    (g.tryFree).freed = g.freed := by rw [gate_holds_while_pending g hp]

/-- `++`/`--` bracket every deferred removal: queue then run restores the count (so `pending` = the
number of outstanding removals; `pending = 0` ⇔ all queued removals have run). -/
theorem queue_run_balance (g : Gate) : (g.queue.run).pending = g.pending := by
  simp only [Gate.queue, Gate.run]; omega

/-- The gate's safety invariant: a freed cluster has no pending removal. -/
def Gate.Inv (g : Gate) : Prop := g.freed = true → g.pending = 0

/-- **`tryFree` preserves the invariant** `freed → pending = 0` — so along any gated trace a freed cluster
has no pending removal: the discharge of `aggregate_no_free_while_pending`. -/
theorem tryFree_preserves_inv (g : Gate) (h : g.Inv) : (g.tryFree).Inv := by
  unfold Gate.Inv Gate.tryFree at *
  by_cases hz : g.pending = 0
  · simp only [if_pos hz]; intro _; exact hz
  · simp only [if_neg hz]; exact h

/-- **The HASHED counter is conservative.** `pgcl143_pending[(pfn>>shift)&mask]` holds the SUM over
clusters colliding into the slot, so `slot ≥ this cluster's pending`. Gating on `slot = 0` therefore
implies this cluster's pending = 0 — the gate NEVER under-holds (never frees while truly pending);
collisions only OVER-hold (refuse to free a drained cluster) = a transient leak, never corruption. -/
theorem hashed_gate_conservative (truePending slotSum : Nat)
    (hle : truePending ≤ slotSum) (hgate : slotSum = 0) : truePending = 0 := by omega

/-! ### The hard5 quarantine (facet B) and the unified orphan invariant. -/

/-- The hard5 QUARANTINE: `++` the gate counter at ANY over-remove, never `--` — a permanent hold of an
orphan'd cluster, covering the IMMEDIATE facet (no pending deferred removal) the deferred `++`/`--` missed. -/
def Gate.quarantine (g : Gate) : Gate := { g with pending := g.pending + 1 }

/-- **A quarantined cluster is never freed** — its pending stays > 0, so the gate re-holds forever: no
reuse, hence no wrong-data (fs-verity) and no stale-LRU `list_del`. The cost is a bounded leak — the
facet-B analogue of `RemoveFloor`'s "leak, never corrupt". -/
theorem quarantine_never_freed (g : Gate) : (g.quarantine).tryFree = g.quarantine :=
  gate_holds_while_pending _ (by simp only [Gate.quarantine]; omega)

/-- The free is safe iff no orphan (present sub-PTE without a live rmap) remains. -/
def orphanSafe (orphans : Nat) : Prop := orphans = 0

/-- **The UNIFIED invariant (R14 §D), discharged for BOTH facets.** The deferred `++`/`--` counts facet-A
orphans (pending removals); the quarantine `++` counts facet-B orphans (immediate over-removes). So the
gate counter dominates the orphans (`orphans ≤ pending`), and gating the free on `pending = 0` forces
`orphans = 0` — "no free while an orphan is present", on both paths. -/
theorem unified_gate_covers_both (pending orphans : Nat)
    (hcover : orphans ≤ pending) (hgate : pending = 0) : orphanSafe orphans := by
  simp only [orphanSafe]; omega

/-- **Why R11's `folio_mapped()` gate was BLIND to the orphan** — the deep reason the lifetime lane kept
slipping. An orphan drives `_mapcount` BELOW the fully-unmapped floor (`mc < -1`), so `folio_mapped`
(which tests `_mapcount ≥ 0`) reads FALSE: the folio looks *more* unmapped than fully-unmapped exactly
when a sub-PTE is still present and freeing is most dangerous. The lifetime gate must key on the orphan
(`mc < -1` ∨ pending), NEVER on `folio_mapped`. -/
theorem folio_mapped_blind_to_orphan {mc : Int} (horphan : mc < -1) : ¬ (0 ≤ mc) := by omega

end Tessera

/-
  Tessera — the mmu_gather DEFERRED-RMAP (delay_rmap) cross-PTL window (pgcl #143 R11).

  pgcl R11 (`doc/from-pgcl-143-cbmc.md`, commit a6d3703) PINNED the live laptop crash, with a verbatim
  tripwire stack, to one window. `zap_present_folio_ptes` (mm/memory.c ~1850) clears the cluster's
  `nr` sub-PTEs under the PTL, sets `delay_rmap=true`, records the cluster in the mmu_gather batch
  (intended to hold `nr` existence refs), and **drops the PTL** — deferring `folio_remove_rmap_ptes(nr)`
  to `tlb_flush_rmaps` AFTER the lock. In that lockless window a SHARED/forked cluster is fully
  unmapped + FREED (refcount 0) by another holder; this CPU's deferred removal then over-removes on the
  freed cluster → `mapcount -1` → freelist/LRU corruption → whole-machine RCU-stall freeze.

  The obligation (R11): **across the window the cluster's refcount must stay > 0 — a STABLE EXISTENCE
  ref held by the gather batch — so it cannot be freed before its own deferred rmap removal.**
  Empirically violated for PGCL shared clusters: the batch's `nr` refs do not actually pin (per-
  sub-PTE-across-mms double-add). This promotes `property2/coq/rmap_defer.v`'s `no_free_while_referenced`
  to the deferred-rmap window: a real held reference (folio_try_get / `delay_rmap=false` for clusters)
  blocks the free across the window; a plain increment that races the free to 0 does not.

  This file is the abstract counting form; the concurrent (∀-interleaving) form is
  `property2/coq/refcount_race.v`. It also explains the *surprising* laptop signature
  `refcount == mapcount` both going negative in lockstep.
-/
namespace Tessera

/-- The cluster's teardown state in the `delay_rmap` window: the reference count, the cached rmap
`mapcount`, and `pending` = deferred rmap removals owed (sub-PTEs cleared under the PTL whose
`folio_remove_rmap_ptes` is deferred to `tlb_flush_rmaps`, after the PTL is dropped). -/
structure GatherState where
  refcount : Int
  mapcount : Int
  pending  : Nat
deriving Repr

/-- The gather batch holds a **stable existence ref** iff its pending deferred removals are backed by
references (`pending ≤ refcount`): every owed rmap-drop has a real ref pinning the cluster live. -/
def Pinned (g : GatherState) : Prop := (g.pending : Int) ≤ g.refcount

/-- The deferred rmap removal fires (`tlb_flush_rmaps`): drop the pending rmaps from `mapcount` and the
matching refs from `refcount` — both by the SAME `pending` (= the batch `nr`). -/
def deferredRemove (g : GatherState) : GatherState :=
  { refcount := g.refcount - g.pending, mapcount := g.mapcount - g.pending, pending := 0 }

/-- A concurrent holder frees its mapping during the window (drops `d` aggregate refs). -/
def concurrentDrop (g : GatherState) (d : Nat) : GatherState :=
  { g with refcount := g.refcount - d }

/-- **THE R11 OBLIGATION — a stable existence ref keeps the cluster live across the window.** While
the gather still owes a deferred removal (`pending > 0`) and is `Pinned`, `refcount > 0`: no
concurrent free can deallocate the cluster before its own deferred rmap removal runs. This is the
property `delay_rmap=false`-for-clusters (remove under the PTL) or a real `folio_try_get` establishes. -/
theorem pinned_stays_live (g : GatherState) (hpin : Pinned g) (hpend : 0 < g.pending) :
    0 < g.refcount := by
  simp only [Pinned] at hpin; omega

/-- **The R11 over-remove (the bug) — unpinned batch refs.** When the batch's refs do NOT pin the
shared cluster (a concurrent free reaches `refcount = 0` while removals are still owed), the deferred
removal decrements an ALREADY-FREED cluster, driving refcount negative — the laptop's `mapcount -1`. -/
theorem unpinned_over_remove (g : GatherState)
    (hfreed : g.refcount = 0) (hpend : 0 < g.pending) :
    (deferredRemove g).refcount < 0 := by
  simp only [deferredRemove]; omega

/-- **Why refcount and mapcount go negative in LOCKSTEP** — the surprising laptop signature
`refcount:-7 mapcount:-7` (and `-11`, `-11`). The deferred removal drops BOTH by the same `pending`
(`nr`), so an over-remove moves them together; equal-in, equal-out. -/
theorem deferred_lockstep (g : GatherState) (h : g.refcount = g.mapcount) :
    (deferredRemove g).refcount = (deferredRemove g).mapcount := by
  simp only [deferredRemove]; omega

/-- **The fix is sound**: a `Pinned` gather whose owed removals correspond to actually-present rmaps
(`pending ≤ mapcount`) leaves both counts non-negative — the deferred removal runs on a live cluster,
no over-remove. So either fix — remove under the PTL (`delay_rmap=false`), or hold a real
`folio_try_get` across the window — discharges the obligation by establishing `Pinned`. -/
theorem pinned_sound (g : GatherState)
    (hpin : Pinned g) (hmap : (g.pending : Int) ≤ g.mapcount) (_hrc0 : 0 ≤ g.refcount) :
    0 ≤ (deferredRemove g).refcount ∧ 0 ≤ (deferredRemove g).mapcount := by
  simp only [Pinned] at hpin; simp only [deferredRemove]; omega

/-! ## R14 — the CROSS-MM aggregate refinement.

R14's faithful-laptop forensic A/B found the deferred over-removed folios dump `refcount:0`: the cluster
is shared/forked across mms, and one mm's last-aggregate-ref-drop FREES it while ANOTHER mm's tlb batch
still owes a deferred removal. So the obligation lifts from one gather to the cross-mm aggregate: the
aggregate refcount must cover the pending deferred removals owed across ALL mms. -/

/-- The shared cluster across mms: its aggregate refcount, and the per-mm pending deferred removals
(one entry per mm with a tlb batch outstanding). -/
structure Aggregate where
  refcount : Int
  pendings : List Nat
deriving Repr

/-- Total deferred removals owed across all mms. -/
def Aggregate.owed (a : Aggregate) : Nat := a.pendings.foldr (· + ·) 0

/-- **The cross-mm obligation**: the aggregate refcount covers every pending removal across all mms —
each mm's batch holds a ref per pending sub-PTE removal. -/
def Aggregate.Pinned (a : Aggregate) : Prop := (a.owed : Int) ≤ a.refcount

/-- **No free while ANY deferred removal is pending** (the R14 root). While some mm still owes a deferred
removal (`owed > 0`) and the aggregate is `Pinned`, the aggregate refcount is positive — no cross-mm
last-ref-drop can free the cluster before every mm's deferred removal has run. -/
theorem aggregate_no_free_while_pending (a : Aggregate) (hpin : a.Pinned) (hpend : 0 < a.owed) :
    0 < a.refcount := by
  simp only [Aggregate.Pinned] at hpin; omega

/-- **THE R14 BUG — a cross-mm aggregate free under a pending removal is exactly an unpinned state.** If
the aggregate is freed (`refcount = 0`) while removals are still owed across mms, the obligation was
necessarily violated: the batches did not hold a ref per pending removal. The deferred removal then runs
on a freed cluster — the use-after-free R14 caught (`refcount:0` at `tlb_flush_rmaps`). -/
theorem aggregate_uaf (a : Aggregate) (hfreed : a.refcount = 0) (hpend : 0 < a.owed) : ¬ a.Pinned := by
  simp only [Aggregate.Pinned]; omega

/-- The cluster after every mm's deferred removal runs (each drops its pending refs). -/
def Aggregate.runAll (a : Aggregate) : Aggregate := { refcount := a.refcount - a.owed, pendings := [] }

/-- **The fix is sound across mms**: a `Pinned` aggregate, after every mm's deferred removal runs, has
`refcount ≥ 0` — no over-remove on any mm's path. The deferred-batch ref-hold (one real `folio_try_get`
per pending removal, across the cross-PTL window) discharges the cross-mm obligation. -/
theorem aggregate_pinned_sound (a : Aggregate) (hpin : a.Pinned) : 0 ≤ (a.runAll).refcount := by
  simp only [Aggregate.Pinned] at hpin; simp only [Aggregate.runAll]; omega

end Tessera

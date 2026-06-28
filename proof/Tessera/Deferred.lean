/-
  Tessera — DEFERRED-MAINTENANCE SAFETY: the general hazard class.

  The bug behind #143 R11 (the `delay_rmap` window), the deferred `folio_put`, the TLB shootdown, and
  every RCU/gather-batch free share ONE shape: an operation `D` on a shared resource `R` is **deferred
  to run after a lock is dropped**, and in the window between scheduling `D` and running it a concurrent
  actor can FREE or reuse `R`. Safety requires a GUARD held across the window. Two guard families:

    (A) **existence-reference** — `R` stays live (`refcount > 0`) because the deferred op holds a stable
        reference per owed unit. #143 R11 (`SharingRace`/`refcount_race`), deferred put (`rmap_defer`),
        RCU free, deferred split/collapse.
    (B) **invalidation-ordering** — `R`'s stale view is invalidated (flush) before reuse. TLB shootdown
        (`Tlb.lean` / `property2/coq/tlb_shootdown.v`).

  This file develops family (A) ONCE, generally, so a new deferral site is a one-line instance: supply
  `(refs, owed)` and discharge the `Pinned` obligation on the code. `doc/deferred-maintenance-catalogue.md`
  enumerates the sites (telix + pgcl/Linux) against this obligation, with proved/unproven status. The
  point R11 taught: we proved the *discipline* (a held ref is safe) but never enumerated the *sites*;
  this closes that gap.
-/
import Tessera.SharingRace

namespace Tessera
namespace Deferred

/-- A **deferred-maintenance window** over a shared resource: `refs` existence references currently
pin the resource (it is LIVE iff `refs > 0`; at `0` it is freed/reusable), and `owed` units of
deferred maintenance are scheduled to run later — each *meant* to hold a reference across the window. -/
structure Window where
  refs : Int
  owed : Nat
deriving Repr

/-- The resource is LIVE (not yet freed / reusable). -/
def Window.live (w : Window) : Prop := 0 < w.refs

/-- **THE OBLIGATION — the deferred op is `Pinned`**: every owed unit is backed by a real existence
reference (`owed ≤ refs`). A correct deferral protocol maintains this for the *whole* window. This is
the single property every family-(A) site must satisfy. -/
def Window.Pinned (w : Window) : Prop := (w.owed : Int) ≤ w.refs

/-- **GENERAL SAFETY — a pinned deferred op never runs on a freed resource.** While maintenance is
owed and the op is pinned, the resource is live: no concurrent free reaches it. -/
theorem pinned_live (w : Window) (hp : w.Pinned) (ho : 0 < w.owed) : w.live := by
  simp only [Window.Pinned] at hp; simp only [Window.live]; omega

/-- A concurrent actor releases `k` of its OWN references during the window (not the deferred op's). -/
def Window.drop (w : Window) (k : Nat) : Window := { w with refs := w.refs - k }

/-- **GENERAL SAFETY ∀-interleaving.** Any amount of concurrent dropping up to the slack beyond the
pinned set (`k ≤ refs − owed`) keeps the op pinned and the resource live — for the whole window,
*however* the concurrent drops interleave (concurrent drops compose to one drop of their sum `k`, so
only `k` matters, not the order). This is the abstract form of `refcount_race.deferred_rmap_window_spec`. -/
theorem drop_keeps_live (w : Window) (k : Nat) (_hp : w.Pinned) (ho : 0 < w.owed)
    (hk : (k : Int) ≤ w.refs - w.owed) : (w.drop k).live := by
  simp only [Window.live, Window.drop]; omega

/-- The deferred op finally runs: it discharges its `owed` maintenance, releasing `owed` references. -/
def Window.run (w : Window) : Window := { refs := w.refs - w.owed, owed := 0 }

/-- **The fix is sound**: a pinned op, when it runs, leaves `refs ≥ 0` — it operated on a live
resource and brought it down to (at worst) free, never below. No over-decrement. -/
theorem run_sound (w : Window) (hp : w.Pinned) : 0 ≤ (w.run).refs := by
  simp only [Window.Pinned] at hp; simp only [Window.run]; omega

/-- **THE GENERAL BUG (an UNPINNED op) — use-after-free is reachable.** If the owed units are NOT
backed by references (`refs < owed` — phantom or double-counted refs; R11's "the batch's nr refs do
not actually pin a shared cluster"), then a concurrent drop of exactly `refs` reaches `refs = 0`
(freed) while maintenance is still owed: the deferred op is now scheduled against a freed resource. -/
theorem unpinned_freed_while_owed (w : Window) (hrefs : 0 ≤ w.refs) (hunpin : w.refs < w.owed) :
    ¬ (w.drop w.refs.toNat).live ∧ 0 < (w.drop w.refs.toNat).owed := by
  simp only [Window.live, Window.drop]
  omega

/-- **The over-decrement consequence**: a deferred op that runs on a freed resource (`refs = 0`) drives
the existence count NEGATIVE — the `mapcount -1` / `refcount:-7` the laptop dumped. -/
theorem run_on_freed_over_decrements (w : Window) (hfreed : w.refs = 0) (ho : 0 < w.owed) :
    (w.run).refs < 0 := by
  simp only [Window.run]; omega

/-- **The LOCKSTEP diagnostic (general).** Two existence counts discharged by the SAME deferred op
(the same `owed`) move together — the general form of the surprising `refcount == mapcount` both going
negative. So a paired-count-equal-and-negative signature *is* a same-`owed` over-run: look for a
deferred-maintenance window. -/
theorem run_lockstep (a b : Window) (href : a.refs = b.refs) (hown : a.owed = b.owed) :
    (a.run).refs = (b.run).refs := by
  simp only [Window.run]; omega

/-! ## Instances — the catalogue, mechanized

Each deferral site is this `Window` with `(refs, owed) = (the resource's existence-reference count,
the deferred-maintenance units owed across the window)`. The obligation `Pinned` and `pinned_live`
apply uniformly; a site is *proved safe* once its code is shown to maintain `Pinned`. -/

/-- **#143 R11 — `delay_rmap` deferred rmap removal** is an instance: a `SharingRace.GatherState`
(refcount, mapcount, pending) is this `Window` via `(refcount, pending)`. -/
def ofGather (g : GatherState) : Window := ⟨g.refcount, g.pending⟩

theorem gather_is_pinned (g : GatherState) : (ofGather g).Pinned ↔ Pinned g := Iff.rfl

/-- `SharingRace.pinned_stays_live` is now a *corollary* of the general `pinned_live` — the R11 site
inherits safety from the general theory, not a bespoke proof. -/
theorem gather_live_of_general (g : GatherState) (hp : Pinned g) (ho : 0 < g.pending) :
    0 < g.refcount :=
  pinned_live (ofGather g) hp ho

/-- **Deferred `folio_put` (tlb-batch)** — the `rmap_defer.v` site: `owed` = deferred puts queued in
the gather, `refs` = the folio refcount; the gather must hold a ref per queued put. Same obligation. -/
example (refs : Int) (owed : Nat) (hp : Window.Pinned ⟨refs, owed⟩) (ho : 0 < owed) :
    Window.live ⟨refs, owed⟩ := pinned_live _ hp ho

/-- **RCU-deferred free** — `owed` = pending RCU callbacks freeing the node, `refs` = readers in the
grace period holding the node live. The same `pinned_live` gives "no reader sees a freed node". -/
example (refs : Int) (owed : Nat) (hp : Window.Pinned ⟨refs, owed⟩) (ho : 0 < owed) :
    Window.live ⟨refs, owed⟩ := pinned_live _ hp ho

end Deferred
end Tessera

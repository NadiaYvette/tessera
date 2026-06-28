/-
  Tessera — RCU-DEFERRED FREE: wiring deferred-maintenance catalogue ROW #4 (`call_rcu` on a shared node).

  Grounded in `mm/mmu_gather.c` (`tlb_remove_table_free` → `call_rcu(&batch->rcu, tlb_remove_table_rcu)`):
  a freed PAGE-TABLE page is handed to `call_rcu`, not freed immediately. Why: lockless software
  page-table walkers — `gup_fast` — walk the page tables under `rcu_read_lock()` *without* taking the
  page-table locks. A reader holds a raw pointer into a page-table page with no refcount. If that page
  were freed while a walker still held the pointer, the walker would dereference freed memory.

  RCU's contract: the deferred free runs only after a GRACE PERIOD — a period after which every reader
  that began before the node was unlinked has exited (passed through a quiescent state on every CPU). So
  the free is gated on `readers → 0`. The "reference" here is not a refcount but the SET OF IN-FLIGHT
  READERS; the grace period is the mechanism that waits for it to drain. The catalogue maps it
  `readers = refs`: the readers ARE the existence references, and the grace period realises `Pinned` by
  construction. Distinct from a refcount guard — there is no per-object counter — yet the same obligation.
-/
import Tessera.Deferred
import Tessera.Incarnation

namespace Tessera
namespace Deferred

/-- An RCU-deferred free. `readers` = pre-existing RCU read-side critical sections (e.g. `gup_fast`
walkers) that may still hold a pointer to the unlinked node; they drain over the grace period. `freed`
= whether the deferred free (the `call_rcu` callback) has run yet. -/
structure Rcu where
  readers : Nat
  freed   : Bool
deriving Repr

/-- The node is live (safe to dereference) while it has not been freed. -/
def Rcu.live (r : Rcu) : Prop := r.freed = false

/-- **The grace-period gate** — the RCU contract: the deferred free runs only after every pre-existing
reader has exited, so `freed → readers = 0`. `call_rcu` (after the unlink) establishes exactly this. -/
def Rcu.gpGated (r : Rcu) : Prop := r.freed = true → r.readers = 0

/-- **THE RCU GUARANTEE — no reader ever touches freed memory.** While any pre-existing reader is still
in its critical section, a gated free has not run: the node is live. (`gup_fast` never dereferences a
page-table page freed under it.) -/
theorem rcu_reader_safe (r : Rcu) (hg : r.gpGated) (hr : 0 < r.readers) : r.live := by
  simp only [Rcu.live, Rcu.gpGated] at *
  cases hf : r.freed with
  | false => rfl
  | true => rw [hf] at hg; simp only [forall_const] at hg; omega

/-- The deferred free actually running (the `call_rcu` callback fires). -/
def Rcu.doFree (r : Rcu) : Rcu := { r with freed := true }

/-- Freeing AFTER the grace period (readers fully drained) preserves the gate — the safe path. -/
theorem free_after_gp_safe (r : Rcu) (hdrained : r.readers = 0) : (r.doFree).gpGated := by
  simp only [Rcu.gpGated, Rcu.doFree]; exact fun _ => hdrained

/-- **THE BUG — a missing grace period** (`kfree` instead of `call_rcu`, or freeing before the unlink's
grace period elapses). Freeing while readers are still in flight breaks the gate: a `gup_fast` walker
holds a pointer into freed memory — use-after-free. -/
theorem free_before_gp_uaf (r : Rcu) (hr : 0 < r.readers) : ¬ (r.doFree).gpGated := by
  simp only [Rcu.gpGated, Rcu.doFree]
  intro h; exact absurd (h trivial) (by omega)

/-- RCU as a `Deferred.Window` (catalogue: `readers = refs`). The in-flight readers ARE the existence
references; the deferred free is owed against every one of them; the grace period realises `Pinned` by
waiting for `refs` to drain to zero before running the free. -/
def Rcu.toWindow (r : Rcu) : Window := { refs := r.readers, owed := r.readers }

/-- The same family: while any reader is in flight the node is live, inherited from the general
`pinned_live` rather than proved bespoke — the grace period is just how `refs → 0` is detected without a
counter. -/
theorem rcu_pinned_live (r : Rcu) (hr : 0 < r.readers) : r.toWindow.live :=
  pinned_live r.toWindow (by simp only [Window.Pinned, Rcu.toWindow]; omega)
    (by simp only [Rcu.toWindow]; omega)

/-- The grace period blocks reincarnation: the node is not freed while readers hold it, so it cannot be
freed+reused under a reader — a reader never observes a reincarnated node (`pinned_inc_correct`; the
type-stable `SLAB_TYPESAFE_BY_RCU` variant is the weaker form where reuse is allowed but kept same-type). -/
theorem rcu_inc_correct (r : Rcu) (p : Pfn) (e : Nat)
    (hr : 0 < r.readers) (hpr : p.refs = r.toWindow.refs) (he : p.inc = e) :
    IncCorrect p e ∧ ¬ CanReincarnate p :=
  pinned_inc_correct r.toWindow p e hpr he
    (by simp only [Window.Pinned, Rcu.toWindow]; omega) (by simp only [Rcu.toWindow]; omega)

end Deferred
end Tessera

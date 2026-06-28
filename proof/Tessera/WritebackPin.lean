/-
  Tessera — SWAP/EVICTION WRITEBACK REF-PIN: wiring deferred-maintenance catalogue ROW #8, ref-pin half.

  Row #8 (swap/eviction deferred writeback) carries TWO obligations. The *content round-trip* — that an
  evicted folio rematerialises with its bytes intact — is already proved in `Eviction.lean`. This file
  wires the *ref-pin* half: the folio under writeback must stay live (incarnation fixed) until the IO
  completes, so the deferred free never races an in-flight DMA into the folio's pages.

  The mechanism in `mm/page_io.c` (`swap_writepage_bdev_async`):

      bio_add_folio_nofail(bio, folio, ...);   -- the IO references the folio's pages
      folio_start_writeback(folio);            -- PG_writeback set: the window OPENS
      folio_unlock(folio);                     -- the lock is DROPPED here...
      submit_bio(bio);                         -- ...BEFORE the async IO is even submitted
      // ... an arbitrary time later, on an IRQ:
      //   end_swap_bio_write -> folio_end_writeback(folio)   -- the window CLOSES

  This is the purest deferred-maintenance window in the catalogue: **no lock spans it.** Between
  `start` and `end` the only thing keeping the folio from being freed+reused is its reference (the swap
  cache) plus the `PG_writeback` marker the reclaimer honours (`vmscan.c`: `folio_test_writeback` ->
  `folio_wait_writeback`). Because the window closes on an external IRQ at an *uncontrolled* time, the
  guarantee we need is order-independence — and that is exactly what `Deferred.drop_keeps_live`
  (∀-interleaving) supplies: any concurrent reclaim up to the slack keeps the folio live *however* it
  interleaves with the completion. Same `Pinned` obligation, hardest window.
-/
import Tessera.Deferred
import Tessera.Incarnation

namespace Tessera
namespace Deferred

/-- Writeback ref-pin state. `refs` = the folio's refcount (incl. the swap-cache hold); `inflight` =
the IO units owed — pages under writeback. `PG_writeback` set ⟺ `inflight > 0`. -/
structure Writeback where
  refs     : Int
  inflight : Nat
deriving Repr

/-- `folio_test_writeback`: the window is open — an IO is in flight. -/
def Writeback.underIO (wb : Writeback) : Prop := 0 < wb.inflight

/-- The writeback as a deferred-maintenance `Window`: the guard is the held refs, the owed maintenance
is the in-flight IO that must complete before the folio may be freed. -/
def Writeback.toWindow (wb : Writeback) : Window := { refs := wb.refs, owed := wb.inflight }

/-- The obligation: the swap-cache/bio reference backs each in-flight IO unit. -/
def Writeback.Pinned (wb : Writeback) : Prop := wb.toWindow.Pinned

/-- **The writeback hold keeps the folio LIVE across the IO** — it cannot be freed while writeback is
in flight (`pinned_live`). This is what the reclaimer's `folio_test_writeback` → `folio_wait_writeback`
guard enforces dynamically. -/
theorem wb_pinned_live (wb : Writeback) (hp : wb.Pinned) (hio : wb.underIO) :
    wb.toWindow.live :=
  pinned_live wb.toWindow hp hio

/-- **THE ASYNC ANGLE — order-independence is the whole game.** Because the window closes on an
external IO-completion IRQ at an uncontrolled time, safety cannot depend on *when* anything runs. The
∀-interleaving theorem delivers exactly that: any concurrent reclaim dropping up to the slack
(`k ≤ refs − inflight`) keeps the folio live *however* it interleaves with the completion. -/
theorem wb_drop_keeps_live (wb : Writeback) (k : Nat) (hp : wb.Pinned) (hio : wb.underIO)
    (hk : (k : Int) ≤ wb.refs - wb.inflight) : (wb.toWindow.drop k).live :=
  drop_keeps_live wb.toWindow k hp hio (by simp only [Writeback.toWindow]; exact hk)

/-- **THE BUG — free under in-flight IO.** If the IO is NOT backed by a real ref (`refs < inflight` —
e.g. the swap-cache ref was dropped early), a concurrent reclaim drop reaches `refs = 0` while the IO
is still owed: the in-flight DMA now writes into a freed (and possibly reused) folio. -/
theorem free_under_io_uaf (wb : Writeback) (hrefs : 0 ≤ wb.refs) (hunpin : wb.refs < wb.inflight) :
    ¬ (wb.toWindow.drop wb.toWindow.refs.toNat).live
      ∧ 0 < (wb.toWindow.drop wb.toWindow.refs.toNat).owed :=
  unpinned_freed_while_owed wb.toWindow hrefs (by simp only [Writeback.toWindow]; exact hunpin)

/-- **The deferred free is sound** once the IO is discharged: after `folio_end_writeback` the reclaim
free brings the count to (at worst) zero, never below — no over-decrement (`run_sound`). -/
theorem end_writeback_sound (wb : Writeback) (hp : wb.Pinned) : 0 ≤ (wb.toWindow.run).refs :=
  run_sound wb.toWindow hp

/-- **The writeback hold blocks reincarnation across the IO** — the folio cannot be freed+reused while
an IO is in flight (`pinned_inc_correct`), so the DMA always lands in the incarnation it was submitted
against. The same incarnation guard as #143 and migration, here spanning an interrupt-bounded window. -/
theorem wb_inc_correct (wb : Writeback) (p : Pfn) (e : Nat)
    (hp : wb.Pinned) (hio : wb.underIO) (hpr : p.refs = wb.toWindow.refs) (he : p.inc = e) :
    IncCorrect p e ∧ ¬ CanReincarnate p :=
  pinned_inc_correct wb.toWindow p e hpr he hp hio

end Deferred
end Tessera

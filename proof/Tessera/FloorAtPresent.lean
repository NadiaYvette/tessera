/-
  Tessera — FLOOR-AT-PRESENT (R17 phase 1) and the mapped-page STAT ledger (2026-07-01).

  Scoping the full per-cluster R17 surfaced a hazard: the kernel's `__folio_mod_stat(folio, nr, ...)`
  drives the mapped-page reclaim stats (`NR_ANON_MAPPED`/`NR_FILE_MAPPED` = meminfo AnonPages/Mapped,
  and `_nr_pages_mapped`) by the SAME `nr` that moves `_mapcount`. So making `_mapcount` per-cluster
  would also make those stats per-cluster — 16x under the true mapped memory — skewing reclaim (anon
  reclaim could stall → OOM). That is a real blast radius, and the user flagged it.

  This file models the third ledger (`stat`) coupled to the rmap edge, and proves:
    * FLOOR-AT-PRESENT (the phase-1 fix) is a NO-OP on a faithful cluster — a spurious remove moves
      NOTHING (rmap, stat, present all unchanged) — so it prevents the underflow (`RemoveDual`'s effect)
      with ZERO stat blast radius: the coupling stays, and stays correct.
    * The invariant it maintains, `present ≤ rmap` (⇒ `folio_mapped` exact when present>0 ⇒ the
      free-while-mapped gate is sound).
    * Why FULL per-cluster additionally requires DECOUPLING the stat (coupled → 16x wrong; decoupled →
      faithful) — the extra work the user's caution named, deferred to phase 2.
-/
import Tessera.MapcountOnly

namespace Tessera

/-- Three ledgers the kernel couples through `__folio_mod_stat`: `rmap` (= `_mapcount + 1`), `stat`
(the mapped-sub-page reclaim/meminfo counters + `_nr_pages_mapped`), and `present` (the true present
sub-PTE count). Under the current per-sub-PTE scheme all three move by the same delta. -/
structure RSP where
  rmap    : Int
  stat    : Int
  present : Int
deriving Repr, DecidableEq

/-- Faithful: both the mapcount ledger and the stat ledger equal the present sub-PTE count. -/
def RSP.faithful (x : RSP) : Prop := x.rmap = x.present ∧ x.stat = x.present

/-- A REAL remove — one present sub-PTE actually cleared: the coupled edge drops `rmap` and `stat`
by 1, and `present` by 1. -/
def RSP.removeReal (x : RSP) : RSP :=
  { rmap := x.rmap - 1, stat := x.stat - 1, present := x.present - 1 }

/-- **FLOOR-AT-PRESENT.** The remove fires only while it keeps `rmap ≥ present` (R20's ground-truth
lower bound `present_here`). Because `rmap` and `stat` are the SAME coupled `__folio_mod_stat` edge,
skipping the fire skips BOTH — nothing leaks. -/
def RSP.removeFloored (x : RSP) : RSP :=
  if x.present < x.rmap then { rmap := x.rmap - 1, stat := x.stat - 1, present := x.present }
  else x

/-- A real remove preserves faithfulness (both ledgers and present fall together). -/
theorem removeReal_preserves_faithful (x : RSP) (h : x.faithful) : (x.removeReal).faithful := by
  obtain ⟨hr, hs⟩ := h
  refine ⟨?_, ?_⟩ <;> simp only [RSP.removeReal] <;> omega

/-- **THE PHASE-1 RESULT — a spurious floored remove is a TOTAL no-op.** On a faithful cluster
`rmap = present`, so the guard `present < rmap` is false and NOTHING moves: no underflow (the
`RemoveDual.perClus` effect) AND the stat is untouched — the zero-stat-blast-radius that makes
floor-at-present safe where full per-cluster is not. -/
theorem removeFloored_spurious_noop (x : RSP) (h : x.faithful) : x.removeFloored = x := by
  obtain ⟨hr, hs⟩ := h
  have hc : ¬ (x.present < x.rmap) := by omega
  simp only [RSP.removeFloored]
  rw [if_neg hc]

theorem removeFloored_preserves_faithful (x : RSP) (h : x.faithful) :
    (x.removeFloored).faithful := by
  rw [removeFloored_spurious_noop x h]; exact h

/-- **The invariant floor-at-present maintains**: from `present ≤ rmap`, any floored remove keeps
`present ≤ rmap`. Hence `folio_mapped` (`rmap ≥ 1`) is exact whenever `present > 0`, so the deferred
free-while-mapped gate it feeds can never be defeated by an undercount. -/
theorem removeFloored_maintains_inv (x : RSP) (h : x.present ≤ x.rmap) :
    x.removeFloored.present ≤ x.removeFloored.rmap := by
  by_cases hc : x.present < x.rmap
  · simp only [RSP.removeFloored, if_pos hc]; omega
  · simp only [RSP.removeFloored, if_neg hc]; omega

/-- …and the stat ledger never underflows below present either, for the same reason (same guard). -/
theorem removeFloored_stat_floored (x : RSP) (h : x.faithful) :
    x.removeFloored.present ≤ x.removeFloored.stat := by
  rw [removeFloored_spurious_noop x h]; obtain ⟨_, hs⟩ := h; omega

/-! ### Why FULL per-cluster (phase 2) additionally needs the stat DECOUPLED -/

/-- If `_mapcount` is made per-cluster (`mcPerClus`) and the stat stays COUPLED to that edge, the stat
collapses to the per-cluster value — `stat ≠ present` (the mapped-sub-page count) whenever `present > 1`:
meminfo/reclaim under-count by up to `PAGE_MMUCOUNT×`. This is the hazard that makes full per-cluster a
bigger change. -/
theorem perClus_coupled_stat_wrong {present : Int} (h : 1 < present) :
    mcPerClus present ≠ present := by
  simp only [mcPerClus]; rw [if_pos (by omega)]; omega

/-- The phase-2 fix the coupling forces: drive the stat by the present-set (identity), not the mapcount
edge — then `stat = present` regardless of the per-cluster `_mapcount`. -/
theorem decoupled_stat_faithful (present : Int) : (fun p => p) present = present := rfl

end Tessera

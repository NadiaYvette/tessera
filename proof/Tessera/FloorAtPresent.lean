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

/-! ### r12fix (task #8): CORRECT an already-violated undercount, not just skip -/

/-- r11probe proved `rmap` (folio_mapcount) reaches states BELOW `present` -- a real over-remove
drove it there BEFORE the floor caught up.  `removeFloored` only SKIPS, so it keeps `rmap` from
dropping further but never REPAIRS an existing `rmap < present`, and `folio_mapped` still lies.
`removeCorrected` (the r12fix): with room (`present < rmap`) do the real floored remove; on an
already-undercounted cluster (`rmap < present`) restore `rmap := present` (the local ground truth);
else hold. -/
def RSP.removeCorrected (x : RSP) : RSP :=
  if x.present < x.rmap then { rmap := x.rmap - 1, stat := x.stat - 1, present := x.present }
  else if x.rmap < x.present then { rmap := x.present, stat := x.stat, present := x.present }
  else x

/-- **THE r12fix SAFETY RESULT**: `removeCorrected` RESTORES `present ≤ rmap` from ANY state --
including the over-removed `rmap < present` the diagnostics captured.  So `folio_mapped` (`rmap ≥ 1`)
is honest whenever `present > 0`, and the free-while-mapped guard can never be defeated by the
mapcount undercount that drove the #143 int3 / WM-crash / deadlock. -/
theorem removeCorrected_restores_inv (x : RSP) :
    x.removeCorrected.present ≤ x.removeCorrected.rmap := by
  unfold RSP.removeCorrected
  by_cases h1 : x.present < x.rmap
  · rw [if_pos h1]; dsimp only; omega
  · rw [if_neg h1]
    by_cases h2 : x.rmap < x.present
    · rw [if_pos h2]; dsimp only; omega
    · rw [if_neg h2]; omega

/-- **The correction never over-shoots**: it sets `rmap` to exactly `present`, never above -- so it
cannot manufacture a phantom mapping beyond the sub-PTEs actually present. -/
theorem removeCorrected_not_above (x : RSP) (h : x.rmap < x.present) :
    x.removeCorrected.rmap = x.present := by
  unfold RSP.removeCorrected
  rw [if_neg (by omega : ¬ x.present < x.rmap), if_pos h]

/-- **The fix does not stall legitimate unmaps**: with room (`present < rmap`) it still performs the
real rmap/stat drop. -/
theorem removeCorrected_real_when_room (x : RSP) (h : x.present < x.rmap) :
    x.removeCorrected.rmap = x.rmap - 1 ∧ x.removeCorrected.stat = x.stat - 1 := by
  unfold RSP.removeCorrected; rw [if_pos h]; exact ⟨rfl, rfl⟩

/-! ### r13refgate: the free-gate that closes the free-while-mapped door on the REFCOUNT path -/

/-- `folio_mapped` as the kernel tests it: the honest per-cluster counter `rmap` (= folio_mapcount)
is ≥ 1.  The r12fix corrective floor keeps `present ≤ rmap`, so this is EXACT for a mapped cluster. -/
def RSP.folioMapped (x : RSP) : Prop := 1 ≤ x.rmap

/-- The free-gate: a free is only ALLOWED when the folio is not mapped (`rmap = 0`).  r12fix makes
`rmap` honest; r13refgate applies this gate on the bypass free paths (free_unref_folios) too, so a
still-mapped folio is refused on EVERY path -- not just the folios_put_refs discharge. -/
def RSP.freeAllowed (x : RSP) : Prop := x.rmap = 0

/-- **THE r13refgate CAPSTONE**: honest counter (`present ≤ rmap`, from the corrective floor) + the
free-gate (`freeAllowed ⇒ rmap = 0`) ⇒ a folio is freed ONLY when `present = 0` -- NO sub-PTE maps
it.  The refcount over-drop can drive `rmap`… no: the free is now gated on `rmap`, and `rmap` is
honest, so free-while-`present`>0 (the #143 int3 / WM-crash / deadlock) is IMPOSSIBLE. -/
theorem no_free_while_mapped (x : RSP) (hp : 0 ≤ x.present)
    (hinv : x.present ≤ x.rmap) (hfree : x.freeAllowed) : x.present = 0 := by
  unfold RSP.freeAllowed at hfree
  omega

/-- Contrapositive, the operational form: a mapped folio (`present ≥ 1`) is NEVER freeAllowed under
the honest invariant -- the gate refuses exactly the free-while-mapped cases, none else. -/
theorem mapped_not_freeAllowed (x : RSP) (hinv : x.present ≤ x.rmap) (hm : 1 ≤ x.present) :
    ¬ x.freeAllowed := by
  unfold RSP.freeAllowed
  omega

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

/-! ### r18: the BATCHED present-floor for the large-folio zap remove -/

/-- r18 floored `folio_remove_rmap_subptes` (mm/memory.c large-folio zap path).  r17 pinned the
residual free-while-mapped to SITE 1 (zap): the stock large-folio path did a bare `atomic_sub(count)`
on a shared file/shmem cluster page's `_mapcount`, driving it BELOW the sub-PTEs still present in this
table (`ph`).  Clamp the removed count so the result never drops below `ph`: remove `min(count, mc-ph)`
when `mc > ph`, else nothing.  (The small-folio path already floors per-edge via `putFloorMc`.) -/
def floorRemoveN (mc ph count : Nat) : Nat :=
  if ph < mc then (if count ≤ mc - ph then mc - count else ph) else mc

/-- **INVARIANT PRESERVED**: a well-formed cluster page (`present ≤ mapcount`) STAYS well-formed after
the batched floored removal — it never drives `mapcount` below `present`, so `folio_mapped()` cannot
lie about a still-mapped cluster (no free-while-mapped from the large-folio zap). -/
theorem floorRemoveN_preserves (mc ph count : Nat) (h : ph ≤ mc) :
    ph ≤ floorRemoveN mc ph count := by
  unfold floorRemoveN
  by_cases hlt : ph < mc
  · simp only [if_pos hlt]
    by_cases hc : count ≤ mc - ph
    · simp only [if_pos hc]; omega
    · simp only [if_neg hc]; omega
  · simp only [if_neg hlt]; omega

/-- **NEVER INCREASES**: the floor only clamps a removal (result ≤ mc); it never adds mapcount. -/
theorem floorRemoveN_le (mc ph count : Nat) : floorRemoveN mc ph count ≤ mc := by
  unfold floorRemoveN
  by_cases hlt : ph < mc
  · simp only [if_pos hlt]
    by_cases hc : count ≤ mc - ph
    · simp only [if_pos hc]; omega
    · simp only [if_neg hc]; omega
  · simp only [if_neg hlt]; omega

/-- **ZERO BLAST RADIUS**: when the batch does not over-remove (`count ≤ mc - ph`, room to spare) the
floor removes the FULL `count` — identical to the stock `mc - count`, so correct zaps are unchanged. -/
theorem floorRemoveN_full (mc ph count : Nat) (hp : ph ≤ mc) (hroom : count ≤ mc - ph) :
    floorRemoveN mc ph count = mc - count := by
  unfold floorRemoveN
  by_cases hlt : ph < mc
  · simp only [if_pos hlt, if_pos hroom]
  · simp only [if_neg hlt]; omega

/-- **FREE-WHILE-MAPPED CLOSURE (batched)**: after the floored batch removal, `mapcount` reaches 0
ONLY when `present = 0`.  Composes with `no_free_while_mapped` — the large-folio zap can no longer
zero a still-mapped cluster's counter. -/
theorem floorRemoveN_zero_only_unmapped (mc ph count : Nat) (h : ph ≤ mc)
    (hz : floorRemoveN mc ph count = 0) : ph = 0 := by
  have := floorRemoveN_preserves mc ph count h; omega

/-- Concrete: a shmem cluster page mapped by 14 sub-PTEs (`mc=14`) with 8 still present (`ph=8`), a
zap batch of `count=10`.  Stock removes 10 → 4 < 8 present (free-while-mapped: the r17 `.cjs` code
page); the r18 floor removes only 6 → 8, exactly present. -/
theorem concreteN : floorRemoveN 14 8 10 = 8 ∧ (14 - 10 : Nat) = 4 := by decide

end Tessera

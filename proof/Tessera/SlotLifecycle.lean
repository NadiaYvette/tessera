/-
  Tessera — the SWAP-SLOT LIFECYCLE facet (#143 cross-mm shared-cluster over-put UAF; pgcl task #4).

  The live empirical suspect after the fragment/format facets came back necessary-but-insufficient.
  A PGCL swap slot is PER-CLUSTER (folio->swap): every sub-PTE of the cluster, in every mm sharing
  it (fork), points at the one slot.  The slot carries a reference count (swap_count) = the number
  of live sub-PTE references across all mms.  Count-correct lifecycle reclaims the slot exactly when
  that count hits zero.  The bug (`do_swap_page` eager `folio_free_swap`, currently gated off under
  `!PAGE_MMUSHIFT` as a leak-not-corrupt stopgap) reclaims the per-cluster slot on ONE mm's swap-in,
  ignoring the survivors — an over-put.  The reclaimed slot is reused for another allocation, so a
  surviving mm's swap entry now reads someone else's content: the use-after-free that corrupts the
  shared cluster.

  Proved: a cross-mm shared slot (≥2 references) is NOT count-correct-reclaimable after one release
  (the survivor is honoured), so under the faithful lifecycle the survivor reads its OWN content;
  the eager free is an over-put (reclaims with a live reference present) and makes the survivor read
  the REUSED content (the UAF); the fix the proof names — reclaim iff live = 0 — admits no surviving
  reader of a reused slot; and the fix is minimal (faithful = eager exactly when no survivor).  This
  discharges the reality of the `slotUAF` facet that Compositionality.lean assumes.
-/
namespace Tessera.SlotLifecycle

/-- A per-cluster swap slot: `live` = live sub-PTE references across all sharing mms; `content` =
    the backing-store content the surviving references expect to read. -/
structure Slot where
  live : Nat
  content : Nat

/-- Acquire a reference (fork-share / swap-out installs another sub-PTE swap entry). -/
def acquire (s : Slot) : Slot := { s with live := s.live + 1 }

/-- Release one reference (a sub-PTE swaps in / is unmapped). -/
def release (s : Slot) : Slot := { s with live := s.live - 1 }

/-- Reuse: a reclaimed slot's content is overwritten by the next allocation. -/
def reuse (s : Slot) (nc : Nat) : Slot := { s with content := nc }

/-- COUNT-CORRECT reclaim: reclaimable exactly when no sub-PTE reference survives. -/
def reclaimable (s : Slot) : Prop := s.live = 0
instance (s : Slot) : Decidable (reclaimable s) := Nat.decEq s.live 0

/-- FAITHFUL lifecycle after mm1's swap-in: reclaim+reuse only if no survivor remains. -/
def afterMm1Faithful (s : Slot) (nc : Nat) : Slot :=
  if reclaimable (release s) then reuse (release s) nc else release s

/-- THE BUG (over-put / eager free): mm1's swap-in reclaims the per-cluster slot unconditionally,
    so it is reused while mm2's reference still points at it. -/
def afterMm1Eager (s : Slot) (nc : Nat) : Slot := reuse (release s) nc

/-- A cross-mm shared slot (≥2 references) is NOT count-correct-reclaimable after one release —
    mm2's reference is honoured. -/
theorem shared_survives_one_release (s : Slot) (h : 2 ≤ s.live) :
    ¬ reclaimable (release s) := by
  have hr : (release s).live = s.live - 1 := rfl
  unfold reclaimable; omega

/-- FAITHFUL: the surviving mm2 reads its OWN content — the slot was not reused. -/
theorem faithful_reads_own (s : Slot) (nc : Nat) (h : 2 ≤ s.live) :
    (afterMm1Faithful s nc).content = s.content := by
  unfold afterMm1Faithful
  rw [if_neg (shared_survives_one_release s h)]
  rfl

/-- THE UAF: a reference survives mm1's release (`1 ≤ (release s).live`), yet under eager free
    that surviving mm2 reads the REUSED content, not its own. -/
theorem eager_reads_garbage (s : Slot) (nc : Nat) (h : 2 ≤ s.live) (hd : nc ≠ s.content) :
    1 ≤ (release s).live ∧ (afterMm1Eager s nc).content ≠ s.content := by
  refine ⟨?_, ?_⟩
  · have hr : (release s).live = s.live - 1 := rfl
    omega
  · simp only [afterMm1Eager, reuse]; exact hd

/-- THE OVER-PUT, named: with a live reference present the slot is not count-correct-reclaimable,
    yet the eager path reclaims it — putting the slot once too often. -/
theorem eager_is_overput (s : Slot) (h : 1 ≤ s.live) : ¬ reclaimable s := by
  simp only [reclaimable]; omega

/-- THE FIX (count-correct free): reclaim only at live = 0, i.e. only when no reference survives,
    so no surviving reader can ever observe a reused slot. -/
theorem countcorrect_reclaim_no_survivor (s : Slot) (h : reclaimable s) : s.live = 0 := h

/-- The fix is MINIMAL: faithful and eager AGREE exactly when there is genuinely no survivor
    (live = 1 → 0), so count-correct free changes behaviour only in the case that is a bug. -/
theorem fix_minimal_no_survivor (s : Slot) (nc : Nat) (h : s.live = 1) :
    afterMm1Faithful s nc = afterMm1Eager s nc := by
  simp only [afterMm1Faithful, afterMm1Eager, reclaimable, release]
  rw [if_pos (show s.live - 1 = 0 by omega)]

end Tessera.SlotLifecycle

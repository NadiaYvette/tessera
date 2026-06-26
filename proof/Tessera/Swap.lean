/-
  Tessera — Layer A / M2: swap-out / eviction (proof-obligation categories D + F + A;
  pgcl #19, #20).

  Evicting a KAU to backing store must (D) depopulate the `c` per-`M` slots, (F) write
  back any dirty content first — *every* dirty sub-PTE, not a peek at slot 0 — and (A)
  flush (already discharged in `Tlb.lean`).  The pgcl #19 failure mode is a swap
  *encoding* that is per-KAU rather than **per-`M`**: one swap location for the whole
  cluster restores only one of the `c` pages, silently losing the rest (and any dirty
  data they held).

  This file models eviction on the KAU vector of `Kau.lean`: a correct swap-out saves
  the **whole** per-`M` vector (so swap-in is lossless and no dirty page is dropped),
  and the single-location encoding is shown to lose data — a provable error.
-/
import Tessera.Kau

namespace Tessera

/-- A KAU swapped out to backing store: its base and the per-`M` saved slots.  **One
saved entry per `M`-page** (pgcl #19): the swap encoding is per-`M`, not per-KAU, so
every constituent page is independently restorable on swap-in. -/
structure Swapped where
  base  : Nat
  saved : List Slot
deriving Repr

namespace Kau

/-- Free the live vector: every slot becomes absent (frames reclaimed), length kept. -/
def depopulate (k : Kau) : Kau := ⟨k.base, k.slots.map (fun _ => none)⟩

/-- **Swap-out** (correct): save the whole per-`M` vector to backing store, then
depopulate the live KAU.  Saving the entire vector preserves every present — and every
dirty — sub-PTE: one swap location per `M`-page. -/
def swapOut (k : Kau) : Swapped × Kau := (⟨k.base, k.slots⟩, k.depopulate)

/-- **Swap-in**: restore the saved per-`M` vector to a live KAU. -/
def swapIn (sw : Swapped) : Kau := ⟨sw.base, sw.saved⟩

/-- **A buggy swap-out using ONE swap location for the whole KAU** (pgcl #19): it saves
only the first slot, so swap-in restores only one `M`-page; the rest are lost. -/
def swapOutBuggy (k : Kau) : Swapped × Kau := (⟨k.base, k.slots.take 1⟩, k.depopulate)

/-- **Swap-out/swap-in is lossless**: restoring the saved record reproduces the
original KAU exactly — every sub-PTE, dirty content included, survives the round trip
(the per-`M` encoding is correct). -/
theorem swap_roundtrip (k : Kau) : swapIn (swapOut k).1 = k := by
  cases k; rfl

/-- **Swap-out preserves invariant 2** (category D: the depopulated vector still has
`c` per-`M` slots): the live KAU after swap-out is well-formed. -/
theorem swapOut_live_wf {c : Nat} {k : Kau} (h : WF c k) : WF c (swapOut k).2 := by
  obtain ⟨hlen, halign⟩ := h
  refine ⟨?_, halign⟩
  show (k.slots.map (fun _ => none)).length = c
  rw [List.length_map]; exact hlen

/-- **The live KAU is fully depopulated after swap-out**: every remaining slot is
absent, so the physical frames are free to reuse. -/
theorem swapOut_depopulated {k : Kau} {s : Slot} (h : s ∈ (swapOut k).2.slots) :
    s = none := by
  simp only [swapOut, depopulate] at h
  rcases List.mem_map.mp h with ⟨_, _, ha⟩
  exact ha.symm

/-- **No dirty data is dropped** (category F, the writeback obligation): every dirty
sub-PTE of the KAU is preserved in the swap record.  (Correct swap-out saves the whole
vector, so in particular every dirty page.) -/
theorem swapOut_preserves_dirty {k : Kau} {s : Slot} (h : s ∈ k.slots)
    (_hd : Slot.dirty s = true) : s ∈ (swapOut k).1.saved := h

/-- **The per-KAU (single-slot) swap encoding loses data — a provable error** (pgcl
#19).  For a KAU with ≥ 2 present `M`-pages, the buggy swap-out saves only the first,
so swap-in cannot reproduce the KAU: pages are lost. -/
theorem swapOutBuggy_loses_data :
    ∃ k : Kau, swapIn (swapOutBuggy k).1 ≠ k := by
  refine ⟨⟨0, [some ⟨0, ⟨true, true, false⟩, false, false⟩,
               some ⟨1, ⟨true, true, false⟩, false, false⟩]⟩, ?_⟩
  intro hc
  simp [swapIn, swapOutBuggy] at hc

/-- **Dropping a dirty page on swap-out is a provable error** (data loss): the buggy
per-KAU encoding can omit a dirty sub-PTE from the swap record entirely. -/
theorem swapOutBuggy_drops_dirty :
    ∃ (k : Kau) (s : Slot),
      s ∈ k.slots ∧ Slot.dirty s = true ∧ s ∉ (swapOutBuggy k).1.saved := by
  refine ⟨⟨0, [some ⟨0, ⟨true, true, false⟩, false, false⟩,
               some ⟨1, ⟨true, true, false⟩, true, false⟩]⟩,
          some ⟨1, ⟨true, true, false⟩, true, false⟩, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide

end Kau

end Tessera

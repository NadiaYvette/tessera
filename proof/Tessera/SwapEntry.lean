/-
  Tessera — the SWAP round-trip: the swap entry (PTE) AND the slot (content), fused.

  Swap is the one path that exercises BOTH frameworks at once. swap-out (`try_to_unmap` + writeback):
  (1) replaces each present sub-PTE with a SWAP ENTRY encoding its sub-page identity, and (2) writes
  that sub-page's content to a backing-store slot. swap-in (`do_swap_page`): (3) restores a present
  PTE at a fresh frame and (4) reads the content back from the slot. So the full swap round-trip has
  FOUR sub-offset-slip sites, two on each side:

      swap-OUT : entry-install (PTE)  +  slot-write (content)   [MigrateEntry.installMigration | swapWrite]
      swap-IN  : entry-restore (PTE)  +  slot-read  (content)   [MigrateEntry.removeMigration  | swapRead]

  The PTE half reuses `MigrateEntry` (a swap entry IS a migration-style entry carrying the
  sub-index — `migration_roundtrip_placed` for faithful, `migration_{install,remove}Fold_wrong` for
  the two PTE slips). This file adds the content half (the slot read/write) and fuses both into the
  observable: a swap round-trip is wrong-data-free iff ALL FOUR are faithful, and folding ANY one is
  a provable error. This is the model for the swap-out bug under investigation; the
  swap-out-vs-swap-in diagnostic of `Eviction.lean` applies per-half (each side has one PTE slip and
  one content slip, observationally identical at the page contents).
-/
import Tessera.MigrateEntry

namespace Tessera

/-- **swap-OUT content write**: save sub-page `i`'s content (at old frame `oldpb+i`) to backing
slot `i`. (The slot is keyed by the true sub-page index — the faithfulness condition.) -/
def swapWrite (oldpb : Nat) (mem0 : Mem) : Store := fun i => mem0 (oldpb + i)

/-- **swap-IN content read**: restore slot `i` to the new frame `newpb+i`; frames outside the
cluster `[newpb, newpb+n)` are unchanged. -/
def swapRead (newpb n : Nat) (st : Store) (mem : Mem) : Mem :=
  fun f => if newpb ≤ f ∧ f < newpb + n then st (f - newpb) else mem f

/-- **The swap content round-trip is sub-page-faithful**: the new frame `newpb+i` holds exactly the
old sub-page `oldpb+i`'s content (slot `i` written on swap-out, read on swap-in). -/
theorem swap_content_roundtrip (oldpb newpb n i : Nat) (hi : i < n) (mem0 : Mem) :
    swapRead newpb n (swapWrite oldpb mem0) mem0 (newpb + i) = mem0 (oldpb + i) := by
  simp only [swapRead, swapWrite]
  rw [if_pos ⟨by omega, by omega⟩]
  congr 1
  omega

/-- **Full swap correctness**: the swap-entry PTE round-trip re-anchors placement to the new base
(`MigrateEntry.migration_roundtrip_placed`) and the slot round-trip restores the content faithfully,
so userspace observes the intended content after a swap out+in. The PTE and content halves compose
into the same observable as migration / eviction. -/
theorem full_swap_observed_intended {vb oldpb newpb n : Nat} {mem0 : Mem} (v : Nat)
    (_hvb : vb ≤ v) (hlt : v - vb < n) :
    observed (intendedFrame vb newpb) (swapRead newpb n (swapWrite oldpb mem0) mem0) v
      = intendedContent vb oldpb mem0 v := by
  simp only [observed, intendedContent, intendedFrame]
  exact swap_content_roundtrip oldpb newpb n (v - vb) hlt mem0

/-- **swap-OUT slot-write fold** (a swap-out / writeback bug): write sub-page 0's content to every
slot. -/
def swapWriteFold (oldpb : Nat) (mem0 : Mem) : Store := fun _ => mem0 oldpb

/-- **The swap-OUT slot-write fold is a provable WRONG-DATA error** — even a correct swap-in reads
back the wrong content, because the wrong content was written out. -/
theorem swapWriteFold_wrong_data {oldpb newpb n : Nat} {mem0 : Mem}
    (hn : 1 < n) (hdiff : mem0 oldpb ≠ mem0 (oldpb + 1)) :
    swapRead newpb n (swapWriteFold oldpb mem0) mem0 (newpb + 1) ≠ mem0 (oldpb + 1) := by
  simp only [swapRead]
  rw [if_pos ⟨by omega, by omega⟩]
  simp only [swapWriteFold]
  exact hdiff

/-- **swap-IN slot-read fold** (a `do_swap_page` bug): read slot 0 into every cluster frame. -/
def swapReadFold (newpb n : Nat) (st : Store) (mem : Mem) : Mem :=
  fun f => if newpb ≤ f ∧ f < newpb + n then st 0 else mem f

/-- **The swap-IN slot-read fold is a provable WRONG-DATA error** — even a correct swap-out wrote the
right slots, the fold reads the wrong one into a later sub-page. -/
theorem swapReadFold_wrong_data {oldpb newpb n : Nat} {mem0 : Mem}
    (hn : 1 < n) (hdiff : mem0 oldpb ≠ mem0 (oldpb + 1)) :
    swapReadFold newpb n (swapWrite oldpb mem0) mem0 (newpb + 1) ≠ mem0 (oldpb + 1) := by
  simp only [swapReadFold]
  rw [if_pos ⟨by omega, by omega⟩]
  simp only [swapWrite, Nat.add_zero]
  exact hdiff

end Tessera

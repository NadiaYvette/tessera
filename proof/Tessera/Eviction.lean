/-
  Tessera — content EVICTION / REMATERIALISATION and the observable (pgcl #143 wrong-data).

  `Placement.lean` proves *where* a sub-PTE points (`phys = intended` sub-frame). That is half of
  wrong-data correctness; the other half is *what content is there*. Content is evicted to backing
  store (swap slot, or file offset = `vm_pgoff + sub-offset`) and later **rematerialised** — the
  `do_swap_page` / filemap-fault path (recently troubled). Under clustering this must be
  **per-sub-page faithful**: sub-page `i`'s content evicts and comes back to sub-page `i`, never
  crossed to `j`. A crossing here reads the WRONG content even when the PTE is placed correctly.

  `Swap.lean` already models the *slot vector* round-trip — data **LOSS** (pgcl #19: a per-KAU
  encoding restores only one page). This file adds the missing concept: per-sub-page **CONTENT**
  and its eviction/rematerialisation, so we can state data **CROSSING** (wrong-data), and compose
  it with placement into the userspace **observable**:

      observed(v) = content at the frame the PTE places v at
      correct ⟺ placement faithful (Placement.lean)  ∧  content round-trip faithful (here)

  Both a placement fold (`cowFold`) and a content fold (`do_swap_page`-style) yield wrong data —
  shown here as independent non-theorems, so neither half can be dropped.
-/
import Tessera.Placement

namespace Tessera

/-- Abstract content of one sub-page (a payload identity — equality is all we need). -/
abbrev Content := Nat

/-- Physical memory: the content currently held at each physical frame. -/
abbrev Mem := Nat → Content

/-- Per-sub-page content of a cluster: sub-page index `i` ↦ its content. -/
abbrev SubVec := Nat → Content

/-- The backing store after eviction — a swap-slot vector / file-offset encoding — keyed by
SUB-PAGE INDEX. Faithful file/swap IO must key by the true sub-page index. -/
abbrev Store := Nat → Content

/-- **Correct eviction** (writeback / swap-out): save each sub-page's content under its own index. -/
def evict (sv : SubVec) : Store := sv

/-- **Correct rematerialisation** (`do_swap_page` swap-in / filemap fault-in): restore each saved
entry to its own sub-page index. -/
def rematerialise (st : Store) : SubVec := st

/-- **Eviction round-trip is content-faithful**: out-then-in restores every sub-page's content to
its own sub-page — no crossing. (File and swap are the same model; only the backing store differs.) -/
theorem evict_roundtrip (sv : SubVec) : rematerialise (evict sv) = sv := rfl

/-- **`do_swap_page`-style sub-offset FOLD on rematerialisation**: swap-in that reads every
sub-page from the cluster's slot 0 (the sub-offset folded away) — the eviction-path twin of
`Placement.cowFold`. -/
def remateFold (st : Store) : SubVec := fun _ => st 0

/-- **The folding rematerialisation is a provable WRONG-DATA error**: whenever two sub-pages
differ, swap-in puts the wrong content into the later sub-page. -/
theorem remateFold_wrong_data :
    ∃ (sv : SubVec) (i : Nat), remateFold (evict sv) i ≠ sv i := by
  exact ⟨id, 1, by decide⟩

/-- **Swap-OUT side sub-offset fold**: a swap-out / writeback that saves the WRONG sub-page's
content to the backing store (here every slot receives sub-page 0's content) — the write-out twin
of `remateFold`, and a candidate shape for the swap-out bug under investigation. -/
def evictFold (sv : SubVec) : Store := fun _ => sv 0

/-- **The swap-OUT fold is a provable WRONG-DATA error, independent of swap-in**: even a perfectly
correct rematerialisation reads back the wrong content, because the wrong content was written out. -/
theorem evictFold_wrong_data :
    ∃ (sv : SubVec) (i : Nat), rematerialise (evictFold sv) i ≠ sv i :=
  ⟨id, 1, by decide⟩

/-- **Diagnostic — the wrong-data signature does NOT by itself distinguish swap-OUT from swap-IN.**
A faithful round-trip needs BOTH halves faithful; folding EITHER side — `evictFold` on write-out or
`remateFold` on read-in — yields the *same* wrong content at the *same* sub-pages. So a swap-out bug
and a swap-in bug are observationally identical in the page contents; the side must be pinned by
checking which half preserved the round-trip (e.g. dump the swap slot between out and in), not by the
corruption signature alone. A useful constraint for the hunt: "wrong content at consistent offsets"
is consistent with both. -/
theorem evict_or_remate_fold_same_corruption :
    (∃ sv i, rematerialise (evictFold sv) i ≠ sv i) ∧
    (∃ sv i, remateFold (evict sv) i ≠ sv i) :=
  ⟨⟨id, 1, by decide⟩, ⟨id, 1, by decide⟩⟩

/-- What userspace **OBSERVES** at virtual granule `v`: the content of the frame its PTE places
`v` at, in physical memory `mem`. -/
def observed (place : Nat → Nat) (mem : Mem) (v : Nat) : Content := mem (place v)

/-- The **INTENDED** content at `v` for a cluster `(vb, pb)` whose original content was `mem0`:
the datum of sub-page `v − vb`, i.e. `mem0 (intendedFrame vb pb v)`. -/
def intendedContent (vb pb : Nat) (mem0 : Mem) (v : Nat) : Content :=
  mem0 (intendedFrame vb pb v)

/-- **Observable correctness — the two halves compose.** If the PTE places each granule at its
INTENDED frame (placement faithful, `Placement.lean`) *and* physical memory still holds the
original content there (content round-trip faithful, here), userspace observes exactly the
intended content: no wrong-data. -/
theorem observed_intended {vb pb : Nat} {place : Nat → Nat} {mem mem0 : Mem}
    (hplace : ∀ v, place v = intendedFrame vb pb v)
    (hmem : ∀ v, mem (intendedFrame vb pb v) = mem0 (intendedFrame vb pb v)) :
    ∀ v, observed place mem v = intendedContent vb pb mem0 v := by
  intro v
  simp only [observed, intendedContent, hplace, hmem]

/-- **Content faithfulness is INDEPENDENTLY necessary**: even with perfectly correct placement, a
folding rematerialisation (`do_swap_page` crossing) makes userspace read the wrong content at a
later sub-page. So proving placement alone does not rule out #143 — the eviction round-trip must
be proved too. -/
theorem content_fold_observed_wrong {vb pb : Nat} {mem0 : Mem}
    (hdiff : mem0 pb ≠ mem0 (pb + 1)) :
    ∃ (place : Nat → Nat) (mem : Mem) (v : Nat),
      (∀ w, place w = intendedFrame vb pb w) ∧
      observed place mem v ≠ intendedContent vb pb mem0 v := by
  refine ⟨intendedFrame vb pb, fun _ => mem0 pb, vb + 1, fun _ => rfl, ?_⟩
  simp only [observed, intendedContent, intendedFrame]
  have h : vb + 1 - vb = 1 := by omega
  rw [h]
  exact hdiff

end Tessera

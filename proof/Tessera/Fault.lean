/-
  Tessera — Layer A / M2: fault / populate (proof-obligation categories C + D + E + G;
  invariants 2, 3).  The inverse of `unmap`: a page fault installs a sub-PTE into a
  KAU's per-`M` vector; once the KAU is fully and uniformly populated it may PROMOTE to
  a `P`-superpage.

  This file proves the **clustering success guarantee** (../doc/clustering-rationale.md,
  use 1): a fully and uniformly populated KAU meets the superpage promotion precondition
  (invariant 3) — so a full uniform KAU *always* promotes, with no external
  fragmentation.  And it shows the precondition is necessary: a GAPPED KAU (a missing
  `M`-page) or one with DIVERGENT permissions is not promotable — promoting either would
  map an absent page, or impose one permission over a divergent one, through the single
  superpage entry (telix #9 / pgcl #9 territory).

  The refcount bump (G) on populate is the `Backing.add` discipline of `Sharing.lean`
  and the flush (A, on a perm-narrowing re-fault) is `Mprotect.lean`; neither is
  re-proved here.  Tile-level promotion of heterogeneous buddies lives in `Tile.lean`;
  this is the orthogonal `c`-vector → superpage view.
-/
import Tessera.Kau

namespace Tessera

namespace Kau

/-- **Complete**: every one of the KAU's `c` slots is present (fully populated). -/
def Complete (k : Kau) : Prop := ∀ s ∈ k.slots, Slot.present s = true

/-- **Uniform permissions**: every present sub-PTE carries the same permissions `p` —
the invariant-3 precondition for collapsing the `c` `M`-entries into one superpage
entry.  (Physical-frame contiguity is the separate `PromotableF` of `Frames.lean`.) -/
def UniformPerms (p : Perm) (k : Kau) : Prop := ∀ sub, some sub ∈ k.slots → sub.perms = p

/-- **Promotable** (KAU → `P`-superpage): complete and uniform-permissioned. -/
def Promotable (p : Perm) (k : Kau) : Prop := Complete k ∧ UniformPerms p k

/-- **Populate** slot `i` with a sub-PTE — a fault filling one `M`-page. -/
def populate (k : Kau) (i : Nat) (sub : SubPte) : Kau := k.setSlot i (some sub)

/-- A KAU built from `c` contiguous uniform sub-PTEs (physical frame `f0 + i`, common
perms `p`): the result of fully and uniformly populating a fresh KAU. -/
def fullUniform (base f0 : Nat) (p : Perm) (c : Nat) : Kau :=
  ⟨base, (List.range c).map (fun i => some ⟨f0 + i, p, false, false⟩)⟩

/-- **Populate preserves invariant 2** (the fault keeps the `c`-vector structure): it is
a slot update, so the vector still has `c` slots and the base is unmoved. -/
theorem populate_wf {c : Nat} {k : Kau} (h : WF c k) (i : Nat) (sub : SubPte) :
    WF c (populate k i sub) := WF.setSlot h i (some sub)

/-- A fully-uniform KAU is well-formed (its vector has `c` slots, base `P`-aligned). -/
theorem fullUniform_wf {base f0 c : Nat} (p : Perm) (h : c ∣ base) :
    WF c (fullUniform base f0 p c) := by
  refine ⟨?_, h⟩
  show ((List.range c).map (fun i => some (⟨f0 + i, p, false, false⟩ : SubPte))).length = c
  rw [List.length_map, List.length_range]

/-- A fully-uniform KAU is complete (every slot present). -/
theorem fullUniform_complete (base f0 : Nat) (p : Perm) (c : Nat) :
    Complete (fullUniform base f0 p c) := by
  intro s hs
  simp only [fullUniform] at hs
  rcases List.mem_map.mp hs with ⟨i, _, rfl⟩
  rfl

/-- A fully-uniform KAU has uniform permissions (`p`, by construction). -/
theorem fullUniform_uniformPerms (base f0 : Nat) (p : Perm) (c : Nat) :
    UniformPerms p (fullUniform base f0 p c) := by
  intro sub hsub
  simp only [fullUniform] at hsub
  rcases List.mem_map.mp hsub with ⟨i, _, hi⟩
  injection hi with hi
  rw [← hi]

/-- **The clustering success guarantee** (clustering-rationale.md, use 1): a fully and
uniformly populated KAU is well-formed AND meets the superpage promotion precondition —
so a full uniform KAU *always* promotes to a `P`-superpage, with no external
fragmentation.  (This is invariant 3 satisfied constructively by the populate path.) -/
theorem fullUniform_promotable {base f0 c : Nat} (p : Perm) (h : c ∣ base) :
    WF c (fullUniform base f0 p c) ∧ Promotable p (fullUniform base f0 p c) :=
  ⟨fullUniform_wf p h,
   fullUniform_complete base f0 p c, fullUniform_uniformPerms base f0 p c⟩

/-- **A gapped KAU is not promotable** (invariant 3 / category E precondition; the
atomicity/completeness side too): a KAU with a missing `M`-page is not complete, so it
must NOT promote — collapsing it into one superpage entry would map the absent page.
The completeness precondition is necessary (telix #9 / pgcl #9). -/
theorem gapped_not_promotable : ∃ k : Kau, ¬ Complete k := by
  refine ⟨⟨0, [none]⟩, ?_⟩
  intro h
  have hc := h none (by simp)
  simp [Slot.present] at hc

/-- **A KAU with a divergent-permission slot is not promotable** (invariant 3): it can
be complete yet fail uniformity — and collapsing it into one superpage entry would
impose a single permission, silently changing the divergent page's perms.  Uniformity
is necessary, not implied by completeness — the provable error. -/
theorem divergent_not_uniformPerms :
    ∃ (p : Perm) (k : Kau), Complete k ∧ ¬ UniformPerms p k := by
  refine ⟨⟨true, true, false⟩,
          ⟨0, [some ⟨0, ⟨true, true, false⟩, false, false⟩,
               some ⟨1, ⟨true, false, false⟩, false, false⟩]⟩, ?_, ?_⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs'
    · rfl
    · rcases List.mem_singleton.mp hs' with rfl; rfl
  · intro h
    exact absurd (h ⟨1, ⟨true, false, false⟩, false, false⟩ (by decide)) (by decide)

end Kau

end Tessera

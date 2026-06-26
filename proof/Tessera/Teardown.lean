/-
  Tessera — Layer A / M2: exit / teardown (proof-obligation categories C + D + G; the
  sequential half).  The concurrent teardown-vs-live-walk race (telix #3, #17) is
  Property 2 (../property2/); the flush (A) is `Tlb.lean`.

  Exit unmaps an entire address space and frees everything.  The two sequential
  obligations:

    * COMPLETENESS (categories C, D): every resident mapping is released — a teardown
      that stops early leaves a region mapped (a leak / dangling region);
    * the REFCOUNT discipline (category G): a backing object whose last mapper exits
      drops to 0 and becomes reclaimable, while one still shared survives; an
      under-decrementing teardown strands a positive count over an empty site set
      (an unreclaimable leak).

  Built on `Kau.depopulate` (Swap.lean) and the `Backing` discipline (Sharing.lean).
-/
import Tessera.Swap
import Tessera.Sharing

namespace Tessera

/-- An address space's resident mappings: the list of KAUs it maps. -/
abbrev AddrSpace := List Kau

/-- Filtering for present slots over an all-absent vector yields nothing. -/
theorem filter_present_allNone (l : List Slot) :
    (l.map (fun _ => (none : Slot))).filter Slot.present = [] := by
  induction l with
  | nil => rfl
  | cons _ ss ih => exact ih

/-- A depopulated KAU has no present sub-PTEs (every slot was freed). -/
theorem Kau.localMapcount_depopulate (k : Kau) : (Kau.depopulate k).localMapcount = 0 := by
  simp only [Kau.depopulate, Kau.localMapcount, filter_present_allNone, List.length_nil]

namespace AddrSpace

/-- The AS's footprint: total present sub-PTEs across all its KAUs. -/
def footprint (as : AddrSpace) : Nat := (as.map Kau.localMapcount).sum

/-- **Teardown**: depopulate every KAU — release every `M`-page of the address space. -/
def teardown (as : AddrSpace) : AddrSpace := as.map Kau.depopulate

/-- **A buggy teardown that stops after the first KAU** (early exit / partial walk):
the tail is left mapped. -/
def teardownBuggy (as : AddrSpace) : AddrSpace :=
  match as with
  | [] => []
  | k :: ks => Kau.depopulate k :: ks

/-- **Complete teardown releases everything** (the leak-free obligation, categories
C + D): after teardown the address space's footprint is zero — no resident mapping
remains. -/
theorem teardown_footprint_zero (as : AddrSpace) : (teardown as).footprint = 0 := by
  induction as with
  | nil => rfl
  | cons k ks ih =>
      have h1 : (teardown (k :: ks)).footprint
              = Kau.localMapcount (Kau.depopulate k) + (teardown ks).footprint := by
        simp only [teardown, footprint, List.map_cons, List.sum_cons]
      have h2 := Kau.localMapcount_depopulate k
      omega

/-- **Teardown is complete to the granule**: every slot of every torn-down KAU is
absent. -/
theorem teardown_complete {as : AddrSpace} {k : Kau} (hk : k ∈ teardown as)
    {s : Slot} (hs : s ∈ k.slots) : s = none := by
  simp only [teardown, List.mem_map] at hk
  obtain ⟨k0, _, rfl⟩ := hk
  simp only [Kau.depopulate] at hs
  rcases List.mem_map.mp hs with ⟨_, _, ha⟩
  exact ha.symm

/-- **Stopping teardown early leaks — a provable error**: a teardown that releases only
the first KAU leaves the rest mapped, so the footprint stays positive even though the
address space is "torn down." -/
theorem teardownBuggy_leaks :
    ∃ as : AddrSpace, (teardownBuggy as).footprint ≠ 0 := by
  refine ⟨[⟨0, [none]⟩, ⟨1, [some ⟨0, ⟨true, true, false⟩, false, false⟩]⟩], ?_⟩
  decide

end AddrSpace

namespace Backing

/-- **Teardown frees a solely-owned object** (category G): removing all of the (only)
mapper's sites brings the backing object's count to 0 — now reclaimable. -/
theorem teardown_frees_owned {σ : Type} {b : Backing σ} (h : b.WF) :
    (b.remove b.sites.length b.sites.length).mapcount = 0 := by
  have h' : b.mapcount = b.sites.length := h
  show b.mapcount - b.sites.length = 0
  omega

/-- **An under-decrementing teardown strands a leak — a provable error** (category G):
removing all sites but decrementing the count by too little leaves a positive count
over an empty site set — the object is unreclaimable though truly unmapped. -/
theorem teardownLeak_strands :
    ∃ b : Backing Nat, b.WF ∧ (b.remove b.sites.length 0).sites = [] ∧
      (b.remove b.sites.length 0).mapcount ≠ 0 := by
  refine ⟨⟨[1, 2], 2⟩, rfl, ?_, ?_⟩
  · decide
  · decide

end Backing

end Tessera

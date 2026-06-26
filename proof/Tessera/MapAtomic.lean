/-
  Tessera — Layer A / M2: `map` atomicity (category H of ../doc/proof-obligations.md).

  telix's most common real MM bug (catalog #5/#6, 10+ sites): a `map` that installs
  a multi-granule region one `M`-page at a time, bails on a mid-loop failure (e.g. a
  page-table-node allocation OOM), leaves the **partial** mapping in place, and/or has
  its failure result ignored — so the caller proceeds as if the whole region were
  mapped. The contract that forbids this is **all-or-nothing**: a successful `map`
  leaves the *whole* region mapped (and nothing else changed); a failed `map` leaves
  the state *exactly as before* (rollback). A partial outcome reported as success must
  be a provable violation.

  This file models that contract over the abstract mapping (`Mapping`, from `Tlb.lean`)
  and proves:
    * `goodMap` (install the whole region) and `failMap` (roll back) satisfy it;
    * `map_atomic` — *any* contract-satisfying result leaves the region either fully
      mapped or untouched, never partial;
    * `buggyMap_violates` / `buggyMap_demo` — a partial install reported as success
      provably breaks the contract.

  NB this is consistent with partial population being a legal *state* (`Kau.lean`): a
  KAU is populated one granule at a time by *separate* atomic single-granule maps, or
  left gapped by unmap — but a single multi-granule `map` call is all-or-nothing.
-/
import Tessera.Tlb

namespace Tessera

/-- Install every granule of `gs`: a granule is mapped afterward iff it already was,
or it is in `gs`. (The effect of a *successful* `map`.) -/
def installAll (m : Mapping) (gs : List Nat) : Mapping := fun v => m v ∨ v ∈ gs

/-- The region `gs` is fully mapped. -/
def MapsAll (m : Mapping) (gs : List Nat) : Prop := ∀ v ∈ gs, m v

/-- The new mapping keeps everything the old one had. -/
def Preserves (m m' : Mapping) : Prop := ∀ v, m v → m' v

/-- The new mapping changes nothing outside `gs`. -/
def FrameOutside (m m' : Mapping) (gs : List Nat) : Prop := ∀ v, v ∉ gs → (m' v ↔ m v)

theorem installAll_mapsAll (m : Mapping) (gs : List Nat) : MapsAll (installAll m gs) gs := by
  intro v hv; exact Or.inr hv

theorem installAll_preserves (m : Mapping) (gs : List Nat) : Preserves m (installAll m gs) := by
  intro v hv; exact Or.inl hv

theorem installAll_frame (m : Mapping) (gs : List Nat) : FrameOutside m (installAll m gs) gs := by
  intro v hv
  constructor
  · intro h; rcases h with h | h
    · exact h
    · exact absurd h hv
  · intro h; exact Or.inl h

/-- The **all-or-nothing contract** for `map gs`: on success (`some m'`) the whole
region is mapped, the prior mapping is preserved, and nothing outside `gs` changed; on
failure (`none`) there is no obligation — the caller keeps the original mapping. -/
def MapSpec (m : Mapping) (gs : List Nat) : Option Mapping → Prop
  | some m' => MapsAll m' gs ∧ Preserves m m' ∧ FrameOutside m m' gs
  | none    => True

/-- Apply a map result: the new mapping on success, the old one on failure (rollback). -/
def applyResult (m : Mapping) : Option Mapping → Mapping
  | some m' => m'
  | none    => m

/-- **All-or-nothing.** Any contract-satisfying `map` leaves the region either fully
mapped (success) or exactly as before (failure / rollback) — never partially mapped. -/
theorem map_atomic {m : Mapping} {gs : List Nat} {res : Option Mapping}
    (h : MapSpec m gs res) :
    MapsAll (applyResult m res) gs ∨ (∀ v ∈ gs, (applyResult m res) v ↔ m v) := by
  cases res with
  | some m' =>
      left
      obtain ⟨hall, _, _⟩ := h
      exact hall
  | none =>
      right
      intro v _; exact Iff.rfl

/-- The correct `map`: install the whole region, succeed. -/
def goodMap (m : Mapping) (gs : List Nat) : Option Mapping := some (installAll m gs)

theorem goodMap_spec (m : Mapping) (gs : List Nat) : MapSpec m gs (goodMap m gs) :=
  ⟨installAll_mapsAll m gs, installAll_preserves m gs, installAll_frame m gs⟩

/-- A correct `map` that fails: it returns failure and the caller keeps the original
mapping — nothing installed (rollback). -/
def failMap (_ : Mapping) (_ : List Nat) : Option Mapping := none

theorem failMap_spec (m : Mapping) (gs : List Nat) : MapSpec m gs (failMap m gs) := trivial

/-- A **buggy** `map`: it installs only the first `k` granules (the loop bailed
mid-way) yet still reports success. -/
def buggyMap (m : Mapping) (gs : List Nat) (k : Nat) : Option Mapping :=
  some (installAll m (gs.take k))

/-- **A partial map reported as success is a provable contract violation.** If some
granule of the region was left uninstalled — in `gs`, not among the first `k`, and not
already mapped — the buggy result fails the all-or-nothing contract (telix #5/#6). -/
theorem buggyMap_violates {m : Mapping} {gs : List Nat} {k : Nat} {v₀ : Nat}
    (hmem : v₀ ∈ gs) (hmiss : v₀ ∉ gs.take k) (hunmapped : ¬ m v₀) :
    ¬ MapSpec m gs (buggyMap m gs k) := by
  intro h
  obtain ⟨hall, _, _⟩ := h
  rcases hall v₀ hmem with h1 | h2
  · exact hunmapped h1
  · exact hmiss h2

/-- Concrete witness: nothing mapped initially, region `[0,1,2]`, but only the first
two granules installed and success reported — a contract violation. -/
theorem buggyMap_demo :
    ∃ (m : Mapping) (gs : List Nat) (k : Nat), ¬ MapSpec m gs (buggyMap m gs k) := by
  refine ⟨(fun _ => False), [0, 1, 2], 2, ?_⟩
  apply buggyMap_violates (v₀ := 2)
  · decide
  · decide
  · intro h; exact h

end Tessera

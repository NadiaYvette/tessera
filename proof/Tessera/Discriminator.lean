/-
  Tessera — ADJUDICATION: which hypothesis is the #143 kill-init blocker?  A formal discriminator.

  The empirical oracles (the QEMU TCG instrumentation — TLB-based FREE-WHILE-USER-MAPPED + kill-init —
  and the real laptop) PRODUCE counterexamples.  This file is the THEORY that must COVER them and
  DECIDE between the live hypotheses.  We encode each hypothesis as a predicted `Outcome` over a
  `Config` of experiment knobs, pin the oracle's observed outcomes, prove which hypotheses the
  ALREADY-RUN experiments falsify, and — where survivors agree on every run experiment — DERIVE the
  unique discriminator on which they PROVABLY disagree, so one more oracle run decides the fix.

  The live hypotheses (this session's open question — "swap PTEs vs perClus vs a new direction"):
    * H_tlb  — kill-init is stale-TLB (a full flush should fix it).
    * H_swap — kill-init is swap-exclusivity in-place reuse: `do_swap_page` sets AnonExclusive on a
               fork-shared swapped-in cluster -> `do_wp_page` reuses in place -> overwrites a shared
               code page (FINDINGS-143 prime suspect).  SWAP-GATED.
    * H_rmap — kill-init is a rmap/refcount free-while-mapped (SingleRoot facet A: refcount over-drop
               -> early free; the perClus / cross-mm over-remove family).  SWAP-INDEPENDENT.

  Result: the flush-all run already falsifies H_tlb; H_swap and H_rmap both survive every run
  experiment yet make OPPOSITE predictions on `swap off`, so a single swap-off oracle run is the
  deciding factor.  This is the maths reducing three hypotheses to one binary measurement.
-/
import Tessera.SingleRoot

namespace Tessera

/-- The experiment knobs the oracle can turn. -/
structure Config where
  shift    : Nat    -- PAGE_MMUSHIFT (0 = control; 4 = laptop)
  swapOn   : Bool   -- swap enabled
  flushAll : Bool   -- escalate every TLB flush to flush_tlb_all (the TLB discriminator)
deriving DecidableEq

/-- The oracle's observables.  `freeWhileMapped` = the TLB-based FREE-WHILE-USER-MAPPED catch
(objective, mapcount-INDEPENDENT — the secondary stale-TLB phenomenon); `killInit` = the laptop
blocker (PID1 dies). -/
structure Outcome where
  freeWhileMapped : Bool
  killInit        : Bool
deriving DecidableEq

/-- A hypothesis predicts an `Outcome` from a `Config`. -/
abbrev Hyp := Config → Outcome

/-- Sub-PTE clustering is live (pgcl0 control is clean — every hypothesis is sub-PTE-specific). -/
def clustered (c : Config) : Bool := decide (0 < c.shift)

/-! ### The three live hypotheses, as mechanisms. -/

/-- Kill-init IS stale-TLB; a full flush eliminates it. -/
def H_tlb : Hyp := fun c =>
  let live := clustered c && !c.flushAll
  { freeWhileMapped := live, killInit := live }

/-- Kill-init is the swap-exclusivity in-place OVERWRITE — needs clustering AND swap; a full flush
does NOT fix it.  The FREE-WHILE-USER-MAPPED catches are the independent secondary stale-TLB. -/
def H_swap : Hyp := fun c =>
  { freeWhileMapped := clustered c && !c.flushAll,
    killInit        := clustered c && c.swapOn }

/-- Kill-init is a rmap/refcount free-while-mapped (SingleRoot `facetA_overdrop`) — needs clustering,
INDEPENDENT of swap; a full flush does NOT fix it.  Same secondary stale-TLB catches. -/
def H_rmap : Hyp := fun c =>
  { freeWhileMapped := clustered c && !c.flushAll,
    killInit        := clustered c }

/-! ### The oracle's products — observed outcomes of the experiments already run. -/

def cfg_shift0   : Config := { shift := 0, swapOn := true, flushAll := false }
def cfg_shift4   : Config := { shift := 4, swapOn := true, flushAll := false }
def cfg_flushall : Config := { shift := 4, swapOn := true, flushAll := true  }

def obs_shift0   : Outcome := { freeWhileMapped := false, killInit := false }  -- pgcl0 control: clean
def obs_shift4   : Outcome := { freeWhileMapped := true,  killInit := true  }  -- 772 catches + kill-init
def obs_flushall : Outcome := { freeWhileMapped := false, killInit := true  }  -- catches->0, kill persists

/-- A hypothesis is CONSISTENT with the run experiments iff it reproduces every observed outcome. -/
def Consistent (h : Hyp) : Prop :=
  h cfg_shift0 = obs_shift0 ∧ h cfg_shift4 = obs_shift4 ∧ h cfg_flushall = obs_flushall

/-! ### The flush-all run already FALSIFIES the stale-TLB hypothesis. -/

/-- **H_tlb is dead.** It predicts a full flush removes kill-init, but the oracle shows kill-init
PERSISTS under `flushAll` (catches went to 0, init still died) — exactly the FINDINGS-143 resolution. -/
theorem H_tlb_falsified : ¬ Consistent H_tlb := by
  intro h; have h3 := h.2.2
  simp [H_tlb, cfg_flushall, obs_flushall, clustered] at h3

theorem H_swap_consistent : Consistent H_swap := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [H_swap, cfg_shift0, cfg_shift4, cfg_flushall, obs_shift0, obs_shift4, obs_flushall, clustered]

theorem H_rmap_consistent : Consistent H_rmap := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [H_rmap, cfg_shift0, cfg_shift4, cfg_flushall, obs_shift0, obs_shift4, obs_flushall, clustered]

/-! ### The survivors agree on every run experiment — current data cannot separate them. -/

theorem survivors_agree_on_run :
    H_swap cfg_shift0 = H_rmap cfg_shift0 ∧
    H_swap cfg_shift4 = H_rmap cfg_shift4 ∧
    H_swap cfg_flushall = H_rmap cfg_flushall := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [H_swap, H_rmap, cfg_shift0, cfg_shift4, cfg_flushall, clustered]

/-! ### The decisive discriminator: shift 4, SWAP OFF.  The survivors provably disagree. -/

def cfg_swapoff : Config := { shift := 4, swapOn := false, flushAll := false }

/-- On the swap-off experiment the two survivors predict OPPOSITE kill-init: swap-gated H_swap says
init SURVIVES, swap-independent H_rmap says init DIES.  A single binary oracle run refutes one. -/
theorem discriminator :
    (H_swap cfg_swapoff).killInit = false ∧ (H_rmap cfg_swapoff).killInit = true := by
  simp [H_swap, H_rmap, cfg_swapoff, clustered]

theorem opposite_predictions :
    (H_swap cfg_swapoff).killInit ≠ (H_rmap cfg_swapoff).killInit := by
  simp [discriminator]

/-- **THE DECISION (the maths as deciding factor).** Run the swap-off experiment on an oracle that is
not fooled by mapcount (the clean swapfix kernel, swap disabled, the TLB/kill-init instrumentation).
The observed kill-init refutes exactly one survivor — so the binary result PICKS the root cause and the
fix:

  * init still dies (swap-independent) ⇒ **H_rmap** — the rmap/refcount free-while-mapped
    (SingleRoot `facetA`); fix the ledger (count refcount by the true present, `nr = k`).
  * init survives (swap-gated)         ⇒ **H_swap** — exclusivity in-place reuse; fix per-cluster
    swap exclusivity (all 16 sub-PTE swap entries exclusive together).

If the oracle's result contradicts BOTH survivors' wider signatures (e.g. kill-init with neither an
in-place-overwrite nor a present-dangler free), the covering theory is incomplete and a NEW hypothesis
must be added here — the model is the place that demand becomes explicit. -/
theorem decision_refutes_one (observed : Bool) :
    (observed = true  → (H_swap cfg_swapoff).killInit ≠ observed) ∧
    (observed = false → (H_rmap cfg_swapoff).killInit ≠ observed) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> simp [discriminator]

end Tessera

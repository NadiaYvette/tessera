/-
  Tessera — the REMOVE-EDGE BAND-AID safety certificate (pgcl #143 R14 §C/§D).

  R14's §B UPDATE sharpened the diagnosis again. Booting band-aid v1 (a `cmpxchg` floor on `_mapcount`
  plus a compensating `folio_get`) on the laptop killed the underflow corruption (bad_page 0, no LRU
  freeze) but introduced a pcp/buddy free-list corruption: the over-removed folios dump `refcount:0` at
  the deferred over-remove (`tlb_flush_rmaps`) — they are ALREADY FREED, and `folio_get` *resurrected* a
  being-freed page. So the dominant over-remove is a **deferred-rmap use-after-free**: a deferred rmap
  removal runs after the cluster's aggregate refcount reached 0 (a cross-mm aggregate free of a shared
  cluster), with no ref held across the deferred window. That re-opens the lifetime lane in a refined
  form — "free while a deferred rmap removal is pending" — modeled by `Deferred.Pinned` on the
  deferred-rmap window (`SharingRace`/`Incarnation`); the static `CallBalance` invariant is the
  downstream floor.

  This file certifies the DEFENSIVE band-aid that lets the laptop boot while the root (the deferred-rmap
  ref-hold) is pinned — pgcl's §D ask: the remove-edge floor + `folio_try_get` is SAFE (leak, never
  corrupt), and the v1→v2 change (`folio_get` → `folio_try_get`) is exactly what closes the pcp
  corruption.
-/
import Tessera.Incarnation

namespace Tessera

/-! ### The floored remove — `_mapcount` cmpxchg-decrement only while `> -1` (never below the floor). -/

/-- The BUGGY unfloored remove: `_mapcount -= 1` unconditionally. At the fully-unmapped floor `-1` it
underflows to `-2` — the over-remove the probe caught (R13/R14 anchors `mc = -2`). -/
def rawRemove (mc : Int) : Int := mc - 1

theorem raw_underflows {mc : Int} (h : mc = -1) : rawRemove mc = -2 := by
  simp only [rawRemove, h]; rfl

/-- The band-aid remove: decrement only while above the `-1` floor; at `-1` it is a no-op. -/
def flooredRemove (mc : Int) : Int := if -1 < mc then mc - 1 else mc

/-- **The floor never underflows**: from any consistent `_mapcount ≥ -1`, the floored remove stays
`≥ -1`. `_mapcount = -2` is unreachable, so the LRU/free-list underflow corruption cannot occur. -/
theorem floored_no_underflow {mc : Int} (h : -1 ≤ mc) : -1 ≤ flooredRemove mc := by
  simp only [flooredRemove]; split <;> omega

/-! ### The compensating ref — `folio_get` (v1, BUGGY) vs `folio_try_get` (v2, FIX).

`folio_try_get` is `inc-unless-zero`: the same predicate as `Incarnation.CanReincarnate`/`stableref` —
a ref can be taken only while the folio is live (`refs > 0`). -/

/-- `folio_get`: unconditional increment. On a FREED folio (`refs = 0`) it RESURRECTS a being-freed page
→ the pcp/buddy corruption R14 hit (RCU stall in `decay_pcp_high`). -/
def folioGet (refs : Int) : Int := refs + 1

theorem get_resurrects_freed {refs : Int} (h : refs = 0) : 0 < folioGet refs := by
  simp only [folioGet, h]; omega

/-- `folio_try_get`: inc-unless-zero. On a freed folio it is a NO-OP. -/
def folioTryGet (refs : Int) : Int := if 0 < refs then refs + 1 else refs

/-- **v2 fixes v1**: `folio_try_get` leaves a freed folio freed — no resurrection, no pcp corruption. -/
theorem tryget_preserves_freed {refs : Int} (h : refs = 0) : folioTryGet refs = 0 := by
  simp only [folioTryGet]; split <;> omega

/-- …and generally try-get never lifts a non-live folio to live (the `inc-unless-zero` guarantee). -/
theorem tryget_stays_nonpos {refs : Int} (h : refs ≤ 0) : folioTryGet refs ≤ 0 := by
  simp only [folioTryGet]; split <;> omega

/-! ### The band-aid step and its safety. -/

/-- A folio at a band-aid over-remove: its `_mapcount` and aggregate `refs`. -/
structure BandAid where
  mc   : Int
  refs : Int
deriving Repr

/-- One over-remove under the v2 band-aid: floor the `_mapcount`, compensate the caller's ref drop with
`folio_try_get`. -/
def BandAid.step (b : BandAid) : BandAid :=
  { mc := flooredRemove b.mc, refs := folioTryGet b.refs }

/-- **THE BAND-AID IS SAFE — leak, never corrupt** (pgcl R14 §D). From a floored-consistent state
(`_mapcount ≥ -1`): the `_mapcount` stays `≥ -1` (no underflow → no LRU/free-list corruption), and a
freed folio (`refs ≤ 0`) is never resurrected (no pcp/buddy corruption). Both corruption modes closed. -/
theorem bandaid_safe (b : BandAid) (hmc : -1 ≤ b.mc) :
    -1 ≤ (b.step).mc ∧ (b.refs ≤ 0 → (b.step).refs ≤ 0) := by
  refine ⟨?_, ?_⟩
  · simpa only [BandAid.step] using floored_no_underflow hmc
  · intro h; simpa only [BandAid.step] using tryget_stays_nonpos h

/-- The cost side: on a LIVE folio the compensating try-get is an uncancelled increment — the band-aid
never frees a live folio, at the price of a LEAK (safe, but not the root fix). -/
theorem bandaid_no_free_while_live (b : BandAid) (h : 0 < b.refs) : 0 < (b.step).refs := by
  simp only [BandAid.step, folioTryGet, if_pos h]; omega

/-- **Why v1 was unsafe**: the same step with `folio_get` resurrects a freed folio to a positive
refcount — the corruption R14 observed. The one-line v1→v2 change is exactly what closes it. -/
def BandAid.stepV1 (b : BandAid) : BandAid := { mc := flooredRemove b.mc, refs := folioGet b.refs }

theorem bandaid_v1_resurrects (b : BandAid) (h : b.refs = 0) : 0 < (b.stepV1).refs := by
  simpa only [BandAid.stepV1] using get_resurrects_freed h

end Tessera

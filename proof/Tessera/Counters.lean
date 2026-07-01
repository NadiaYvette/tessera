/-
  Tessera — the pgcl COUNTER DISCIPLINE for R17 phase 2: per-cluster _mapcount, per-sub-PTE ref/stat/rss.
  The faithful multi-counter model that SPECIFIES the kernel conversion (2026-07-01).

  The -pgcl4-143fop boot proved the fix is to make `_mapcount` a function of the present-set so
  `folio_mapped()` is exact and the deferred-free gate is sound (MapGate).  Implementing that in the
  kernel means splitting the counters by DISCIPLINE, and the subtlety (which the boot's stat lines made
  concrete) is that they do NOT all move the same way:

    * `_mapcount` (folio): PER-CLUSTER — this mm contributes +1 on its FIRST present sub-PTE of the
      cluster and −1 on its LAST (distinct-mm counting).  This is the R17 change.
    * `refcount`, `NR_{ANON,FILE}_MAPPED` (the meminfo/reclaim stat), `rss`: PER-SUB-PTE — ±k for k
      sub-PTEs mapped/unmapped.  UNCHANGED by R17 (decoupled from the mapcount edge).

  The kernel is stat-neutral under this split BY CONSTRUCTION: the stat drivers are already first/last
  (`atomic_inc_and_test` on add, `mc−1<0` on remove) and the direct sites (do_anonymous_page, COW, fork)
  keep their separate `lruvec_stat`/`folio_ref_add` lines — so moving only the `_mapcount` edges leaves
  every stat untouched.  This file proves the discipline is COHERENT: every counter balances over a
  map/unmap cycle, and the per-cluster `_mapcount` keeps `folio_mapped()` EXACT (= `MapcountOnly.mcPerClus`
  of the present-set), which is what `MapGate` needs.  It is the spec each kernel site must match.
-/
import Tessera.MapGate

namespace Tessera

/-- The full pgcl counter set for one cluster in one mm.  `mapcount` is this mm's contribution to the
folio `_mapcount` (R17: per-cluster / distinct-mm); `refcount`, `stat` (NR_*_MAPPED), `rss` are
per-sub-PTE; `present` is the ground-truth present sub-PTE count in this mm. -/
structure Counters where
  mapcount : Int
  refcount : Int
  stat     : Int
  rss      : Int
  present  : Int
deriving Repr, DecidableEq

/-- ADD `k` sub-PTEs.  The `_mapcount` edge fires (+1) ONLY when this is this mm's first map of the
cluster (`present` was 0); `refcount`/`stat`/`rss` each move by the full `k` (per-sub-PTE). -/
def Counters.addk (c : Counters) (k : Int) : Counters :=
  { mapcount := c.mapcount + (if c.present = 0 then 1 else 0),
    refcount := c.refcount + k,
    stat     := c.stat + k,
    rss      := c.rss + k,
    present  := c.present + k }

/-- REMOVE `k` sub-PTEs.  The `_mapcount` edge fires (−1) ONLY when this is this mm's last unmap
(`present` reaches 0); `refcount`/`stat`/`rss` each move by `k` (per-sub-PTE). -/
def Counters.remk (c : Counters) (k : Int) : Counters :=
  { mapcount := c.mapcount - (if c.present - k = 0 then 1 else 0),
    refcount := c.refcount - k,
    stat     := c.stat - k,
    rss      := c.rss - k,
    present  := c.present - k }

/-- The R17 fidelity invariant: this mm's `_mapcount` contribution equals `folio_mapped()`'s witness of
the present-set — `mcPerClus present` (= `present > 0 ? 1 : 0`).  Exactly what `MapGate.r17Gate` needs. -/
def Counters.faithful (c : Counters) : Prop := c.mapcount = mcPerClus c.present

/-- **ADD preserves fidelity.** Whether or not it is the first map, the per-cluster edge keeps
`mapcount = mcPerClus present` (first: 0→1 as present 0→k>0; subsequent: stays 1 as present grows). -/
theorem addk_preserves_faithful (c : Counters) (k : Int) (h : 0 < k) (hp : 0 ≤ c.present)
    (hc : c.faithful) : (c.addk k).faithful := by
  simp only [Counters.faithful, Counters.addk, mcPerClus] at hc ⊢
  rw [if_pos (show (0:Int) < c.present + k by omega)]
  by_cases hz : c.present = 0
  · rw [if_neg (show ¬(0:Int) < c.present by omega)] at hc
    rw [if_pos hz]; omega
  · rw [if_pos (show (0:Int) < c.present by omega)] at hc
    rw [if_neg hz]; omega

/-- **REMOVE preserves fidelity** (given `k ≤ present`, a real remove).  Last unmap: 1→0 as present→0;
partial: stays 1 as present stays > 0. -/
theorem remk_preserves_faithful (c : Counters) (k : Int) (hle : k ≤ c.present) (hk : 0 < k)
    (hc : c.faithful) : (c.remk k).faithful := by
  simp only [Counters.faithful, Counters.remk, mcPerClus] at hc ⊢
  rw [if_pos (show (0:Int) < c.present by omega)] at hc
  by_cases hz : c.present - k = 0
  · rw [if_pos hz, if_neg (show ¬(0:Int) < c.present - k by omega)]; omega
  · rw [if_neg hz, if_pos (show (0:Int) < c.present - k by omega)]; omega

/-- **CYCLE BALANCE.** From an unmapped baseline, map `k` then unmap `k` returns EVERY counter to
baseline: the per-cluster `_mapcount` edge (+1 first / −1 last) and the per-sub `refcount`/`stat`/`rss`
all cancel.  The coherence obligation each kernel path must meet. -/
theorem cycle_balances (k : Int) :
    (Counters.addk ⟨0, 0, 0, 0, 0⟩ k).remk k = ⟨0, 0, 0, 0, 0⟩ := by
  simp only [Counters.addk, Counters.remk]
  simp

/-- **The consequence for the gate.** A faithful cluster's `_mapcount` reading drives `MapGate.r17Gate`,
so — by `MapGate.r17_no_free_while_mapped` — the deferred-free gate NEVER frees it while present > 0.
The counter discipline of this file is exactly what closes the fop free-while-mapped. -/
theorem faithful_gate_sound (c : Counters) (refcount : Int) (h : 0 < c.present) :
    ¬ (r17Gate c.present refcount).freeWhileMapped :=
  r17_no_free_while_mapped c.present refcount h

end Tessera

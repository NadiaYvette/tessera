/-
  Tessera — the folio_mapped() DEFERRED-FREE GATE, and why an undercounted _mapcount defeats it;
  the structural proof that full R17 (per-cluster mapcount) restores it (the -pgcl4-143fop boot, 2026-07-01).

  The fop boot caught the over-put red-handed with an INDEPENDENT ground-truth scan:
      PGCL143-FILE-OVERPUT rc=1 nr=1 present_before=1 mapcount=0 STILL-MAPPED  (openclaw madvise, shmem .cjs)
  present_before=1 (a sub-PTE is genuinely still present) yet mapcount=0 -> the mapcount is UNDERCOUNTED.
  The free path is folios_put_refs (mm/swap.c:1011), which carries the PROVEN deferred-free gate
  (5ad142d, no_free_while_referenced): when the gather drives _refcount to 0, free ONLY IF
  folio_mapped() reads unmapped; else undo the put and skip the free.  But folio_mapped() reads the
  UNDERCOUNTED mapcount -> false -> the gate is DEFEATED -> the still-mapped cluster is freed -> bad_page.

  The existing ledgers (FloorAtPresent.RSP, MapcountOnly.MRP, FileCacheRef.FileFolio) carry `present ≤ rmap`
  invariants but do NOT model the GATE as the safety mechanism, nor the coupling that makes it a witness:
  the free is REFCOUNT-driven, GATED by folio_mapped() (= mapcount), and an undercounted mapcount makes
  the gate lie.  This file adds that, and proves:
    * per-sub-PTE accumulator mapcount can be undercounted (mapReading 0 while present>0) -> the gate frees
      a still-mapped cluster (free-while-mapped, the bad_page) -- undercount_defeats_gate;
    * per-cluster mapcount (full R17, mcPerClus = function of the present-set) makes folio_mapped() EXACT,
      so the gate NEVER frees while a sub-PTE is present, for ANY refcount -- including an undercounted
      refcount=0 (the fop `rc=1->0`): the corruption becomes a LEAK, not a free-while-mapped
      (r17_gate_never_frees_while_mapped, r17_no_free_while_mapped);
    * under R17 the gate frees EXACTLY when truly unmapped (present=0) -- folio_mapped() is a faithful
      witness of the present-set (r17_frees_iff_unmapped): the gate is sound.
  This is the formal statement of "full R17 is the structural fix" that the enriched detector confirmed.
-/
import Tessera.MapcountOnly

namespace Tessera

/-- A cluster at the deferred free (folios_put_refs, mm/swap.c:1011).  `present` is the GROUND-TRUTH
count of sub-PTEs still mapping it (the independent `present_before` scan).  `refcount` is the aggregate
_refcount the gather is about to leave.  `mapReading` is what `folio_mapped()` returns as its witness
(`> 0` ⇒ "still mapped") — its fidelity depends on the mapcount DISCIPLINE. -/
structure GateState where
  present    : Int      -- ground-truth present sub-PTEs (the present_before scan)
  refcount   : Int      -- aggregate refcount after the gather's drop
  mapReading : Int      -- folio_mapped() witness: > 0 means "still mapped"
deriving Repr, DecidableEq

/-- The deferred-free GATE (5ad142d, mm/swap.c:1011): the free proceeds iff the aggregate put reached
`refcount = 0` AND `folio_mapped()` reads unmapped (`mapReading = 0`).  Otherwise the put is undone and
the free skipped. -/
def GateState.frees (g : GateState) : Prop := g.refcount = 0 ∧ g.mapReading = 0

/-- FREE-WHILE-MAPPED — the free proceeds while a sub-PTE is still present.  The bad_page / corruption. -/
def GateState.freeWhileMapped (g : GateState) : Prop := g.frees ∧ 0 < g.present

/-! ### Per-sub-PTE accumulator mapcount (current) — undercountable, defeats the gate. -/

/-- The observed regime: `present > 0` but the accumulator mapcount reads 0 (undercounted by a spurious
remove / install under-add / split-reset clobber), and the gather drove `refcount` to 0. -/
def undercounted (present : Int) : GateState :=
  { present := present, refcount := 0, mapReading := 0 }

/-- **THE BUG (formal).** With mapcount undercounted to 0 while `present > 0` and `refcount = 0`, the
gate sees `folio_mapped() = false` and FREES a still-mapped cluster.  This is the fop boot's
`rc=1→0 present_before=1 mapcount=0` → bad_page. -/
theorem undercount_defeats_gate {present : Int} (h : 0 < present) :
    (undercounted present).freeWhileMapped :=
  ⟨⟨rfl, rfl⟩, h⟩

/-! ### Per-cluster mapcount (full R17) — folio_mapped() exact, gate sound. -/

/-- The gate state under R17: `folio_mapped()` reads `mcPerClus present` (`MapcountOnly.mcPerClus`,
= `present > 0 ? 1 : 0`) — a FUNCTION of the present-set — whatever the (possibly undercounted) refcount. -/
def r17Gate (present refcount : Int) : GateState :=
  { present := present, refcount := refcount, mapReading := mcPerClus present }

/-- **THE FIX (formal).** Under R17, whenever a sub-PTE is present the gate reads `folio_mapped() = true`,
so it NEVER frees — for ANY refcount, including the undercounted `refcount = 0`.  Hence no
free-while-mapped: the corruption is impossible; an undercounted refcount degrades to a LEAK (the folio
is retained), not a free-while-mapped. -/
theorem r17_gate_never_frees_while_mapped (present refcount : Int) (h : 0 < present) :
    ¬ (r17Gate present refcount).frees := by
  simp only [GateState.frees, r17Gate, mcPerClus, if_pos h]
  rintro ⟨_, h1⟩
  omega

theorem r17_no_free_while_mapped (present refcount : Int) (h : 0 < present) :
    ¬ (r17Gate present refcount).freeWhileMapped := fun hfwm =>
  r17_gate_never_frees_while_mapped present refcount h hfwm.1

/-- **The gate is SOUND under R17**: it frees EXACTLY when the cluster is truly unmapped (`present ≤ 0`)
and `refcount = 0` — never while a sub-PTE is present.  So `folio_mapped()` is a faithful witness of the
present-set, and free ⟺ (unmapped ∧ refcount 0). -/
theorem r17_frees_iff_unmapped (present refcount : Int) :
    (r17Gate present refcount).frees ↔ (present ≤ 0 ∧ refcount = 0) := by
  simp only [GateState.frees, r17Gate, mcPerClus]
  by_cases h : 0 < present
  · rw [if_pos h]
    constructor
    · rintro ⟨_, h1⟩; omega
    · rintro ⟨h2, _⟩; omega
  · rw [if_neg h]
    constructor
    · rintro ⟨hr, _⟩; exact ⟨by omega, hr⟩
    · rintro ⟨_, hr⟩; exact ⟨hr, rfl⟩

/-- **The fop boot witness on one point** `present = 1, refcount = 0` (the observed `rc` hit 0 by the
refcount undercount too): the per-sub-PTE accumulator FREES it (corruption); R17 GATES it (leak).  Both
faces of the same fix on the same state. -/
theorem fop_boot_witness :
    (undercounted 1).freeWhileMapped ∧ ¬ (r17Gate 1 0).frees :=
  ⟨undercount_defeats_gate (by omega), r17_gate_never_frees_while_mapped 1 0 (by omega)⟩

end Tessera

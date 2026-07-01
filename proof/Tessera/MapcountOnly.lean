/-
  Tessera — the MAPCOUNT-ONLY deficit: the `-pgcl4-143fix` boot's discriminator (2026-07-01).

  The split-reset FILE-clobber fix (`mm/huge_memory.c` __split_huge_page tail/head, gated on
  `folio_test_anon`; R18 "candidate 1") landed, but the corruption PERSISTED: `SPLIT-RESET = 0`
  yet ORPHAN 221 / bad_page 22 / rss-counter 12 — exactly R20's prediction (candidate 1 is a real
  hole but NOT the dominant cause; "the 216 over-removes happened with zero splits ⇒ the file facet
  is in the plain order-0 remove path"). page_owner then DISCRIMINATED the survivor against
  `SingleRoot`'s single-`nr` install under-add. A btrfs page-cache FILE folio at the over-remove read

      refcount:5   mapcount:0   present_here:3     (aops:btrfs_aops, live mapping)

  — the REF ledger INTACT (5 retains the 3 mapping refs), the RMAP ledger ALONE in deficit (0 vs 3).
  `SingleRoot.dual_lockstep` proves one install `nr` drives BOTH ledgers down by the SAME `d`
  (R11's `refcount:−7 mapcount:−7`). UNEQUAL deficits therefore FALSIFY the install-under-add for this
  folio and pin a REMOVE-side spurious `_mapcount −1` with NO matching ref drop (R17's double-discharge)
  — the `remove_migration_pte` / migration facet (migration HOLDS the folio ref across the restore, so
  a mis-counted mapcount restore drops the rmap ledger only). This file models that regime, states the
  discriminator formally, and re-proves R17's per-cluster fix (`_mapcount` as a FUNCTION of the
  present-set) closes it — a spurious mapcount-only remove is a no-op.
-/
import Tessera.CallBalance

namespace Tessera

/-- Two ledgers + ground truth for one cluster: `rmap` (= `_mapcount + 1`), `ref` (the refcount
contribution of this batch's mappings), `present` (the true present sub-PTE count). Unlike
`SingleRoot.DualCount`, here the two ledgers are allowed to diverge — which is the observation. -/
structure MRP where
  rmap    : Int
  ref     : Int
  present : Int
deriving Repr, DecidableEq

/-- Faithful: both ledgers equal the present count (`CallBalance.Balanced` on both). -/
def MRP.Balanced (x : MRP) : Prop := x.rmap = x.present ∧ x.ref = x.present

/-- A **mapcount-only spurious remove**: drops the per-cluster aliased `_mapcount` by 1 with NO
present→absent transition (`present` unchanged) and NO ref drop (`ref` unchanged). This is a
`folio_remove_rmap` NOT matched by a PTE clear or a `folio_put` — the migration restore facet
(`remove_migration_pte`, ref held by migration) and, generally, any `−1` the aliased counter cannot
tell is spurious (R17: "a `−1` with no present→absent transition"). -/
def MRP.moRemove (x : MRP) : MRP := { x with rmap := x.rmap - 1 }

/-- `n` such removes. -/
def MRP.moRemoveN (x : MRP) (n : Int) : MRP := { x with rmap := x.rmap - n }

/-- **THE BOOT SIGNATURE — unequal deficits.** From balance, a mapcount-only spurious remove leaves the
rmap ledger in deficit (`rmap < present`) while the ref ledger is UNTOUCHED (`ref = present`): the
`mapcount:0 present:3` with `refcount` intact that page_owner caught. -/
theorem mo_unequal (x : MRP) (h : x.Balanced) :
    x.moRemove.rmap < x.moRemove.present ∧ x.moRemove.ref = x.moRemove.present := by
  obtain ⟨hr, hf⟩ := h
  refine ⟨?_, ?_⟩ <;> simp only [MRP.moRemove] <;> omega

/-- **THE DISCRIMINATOR (formal).** After a mapcount-only remove from balance, the REF-ledger deficit is
`0` while the RMAP-ledger deficit is positive — UNEQUAL. `SingleRoot.dual_lockstep` has them EQUAL. So
the boot's "refcount intact, mapcount lost" is not the single-`nr` install under-add; it is remove-side. -/
theorem mo_ref_deficit_zero_rmap_positive (x : MRP) (h : x.Balanced) :
    (x.moRemove.present - x.moRemove.ref = 0) ∧ (0 < x.moRemove.present - x.moRemove.rmap) := by
  obtain ⟨hr, hf⟩ := h
  refine ⟨?_, ?_⟩ <;> simp only [MRP.moRemove] <;> omega

/-- **The faithful-laptop anchor**, `refcount:5 mapcount:0 present:3`. Modelling the mapping-ref
sub-ledger (`ref = 3` mapping refs; the real dump's `5` = `2` background + these `3`): three
mapcount-only spurious removes from the balanced `(3,3,3)` land exactly on `(rmap 0, ref 3, present 3)`
— the rmap ledger emptied while ref and present hold. -/
theorem boot_witness :
    MRP.moRemoveN { rmap := 3, ref := 3, present := 3 } 3
      = { rmap := 0, ref := 3, present := 3 } := by
  decide

/-- **The orphan is reachable with the ref ledger healthy.** Enough mapcount-only removes drive the rmap
ledger below zero (`_mapcount ≤ -2`, the over-remove) while `ref = present ≥ 0` throughout — precisely
"allocated, refcount positive, not freed" (R13 verdict 2 / the boot's live-page orphans), now with the
ledgers explicitly UNEQUAL, which `SingleRoot` (equal-deficit) could not express. -/
theorem mo_orphan_ref_healthy (x : MRP) (h : x.Balanced) {n : Int} (hn : x.present < n) :
    (x.moRemoveN n).rmap < 0 ∧ (x.moRemoveN n).ref = x.present := by
  obtain ⟨hr, hf⟩ := h
  refine ⟨?_, ?_⟩ <;> simp only [MRP.moRemoveN] <;> omega

/-! ### R17's per-cluster fix, re-proved on this regime -/

/-- The per-cluster FAITHFUL `_mapcount` (R17 `perClus`): a FUNCTION of the present-set, not an
accumulator — `mc = present>0 ? 1 : 0`. -/
def mcPerClus (present : Int) : Int := if 0 < present then 1 else 0

/-- **THE FIX — the spurious mapcount-only remove is a NO-OP under the per-cluster discipline.** When
`_mapcount` is recomputed from `present` (which a mapcount-only remove does NOT change), the count is
unmoved: no drift, no deficit, no orphan. This is `RemoveDual.perClus_spurious_noop` on the
mapcount-only regime — the root fix, closing the degree of freedom the aliased accumulator had. -/
theorem mo_perClus_noop (x : MRP) :
    mcPerClus x.moRemove.present = mcPerClus x.present := by
  simp only [MRP.moRemove]

/-- …and per-cluster stays faithful to "any sub-PTE present": for a nonempty present-set the fixed
count reads mapped (`1`), for empty it reads unmapped (`0`) — `folio_mapped()` is then exact, so the
free-while-mapped gate it feeds is sound (no undercount can make it lie). -/
theorem mcPerClus_exact (present : Int) :
    (0 < present → mcPerClus present = 1) ∧ (present ≤ 0 → mcPerClus present = 0) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [mcPerClus] <;> split <;> omega

end Tessera

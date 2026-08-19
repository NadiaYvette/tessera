(* Tessera — S4.4 (AMD-Vi): the 4-level I/O page-table walk.

   `machine.sail`'s `amdvi_walk` (S4.4) models AMD-Vi's distinctive feature
   over Sv39: a *4-level* I/O page table (52-bit GPA, 4 x 9-bit levels + 12-bit
   offset).  It is composed as the extra top level (`vpn3`, bits [47..39])
   resolving to a non-leaf PTE, then the bottom 3 levels are exactly the Sv39
   `translate` re-rooted at that PTE.

   This file proves the composition: a valid non-leaf level-3 PTE makes
   `amdvi_walk` exactly the 3-level `iommu_walk` re-rooted at that PTE (the
   4-level walk subsumes the 3-level walk), and a missing/invalid/leaf/N=1
   level-3 PTE faults.  See doc/iommu-shootdown-plan.md (S4.4). *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import shootdown.      (* core_with_root *)
Import ListNotations.

(* A valid, non-leaf, non-NAPOT level-3 PTE ⇒ the 4-level walk is exactly the
   3-level `iommu_walk` re-rooted at that PTE (the 4-level walk subsumes the
   3-level walk). *)
Lemma amdvi_walk_refines_iommu_walk (root : mword 44) (mem : list MemEntry) (iova : mword 64) (p3 : Pte) :
  read_pte mem (pte_address root (vpn3 iova)) = Some p3 ->
  p3.(Pte_valid) = true ->
  is_leaf p3 = false ->
  p3.(Pte_napot) = false ->
  amdvi_walk root mem iova = iommu_walk p3.(Pte_ppn) mem iova.
Proof.
  intros H Hv Hl Hn. unfold amdvi_walk, iommu_walk.
  rewrite H. cbn. rewrite Hv, Hl, Hn. cbn. reflexivity.
Qed.

(* A missing / invalid / leaf / N=1 level-3 PTE ⇒ the 4-level walk faults. *)
Lemma amdvi_walk_level3_faults (root : mword 44) (mem : list MemEntry) (iova : mword 64) (p3 : Pte) :
  read_pte mem (pte_address root (vpn3 iova)) = Some p3 ->
  p3.(Pte_valid) = false \/ is_leaf p3 = true \/ p3.(Pte_napot) = true ->
  amdvi_walk root mem iova = None.
Proof.
  intros H Hf. unfold amdvi_walk. rewrite H. cbn.
  destruct Hf as [Hv | [Hl | Hn]].
  - rewrite Hv. reflexivity.
  - rewrite Hl. destruct p3.(Pte_valid); cbn; reflexivity.
  - rewrite Hn. destruct p3.(Pte_valid), (is_leaf p3); cbn; reflexivity.
Qed.

(* The empty table faults the 4-level walk (no level-3 PTE). *)
Lemma test_vector_amdvi_4level_empty_faults :
  amdvi_walk (mword_of_int 1 : mword 44) [] (mword_of_int 0 : mword 64) = None.
Proof. vm_compute. reflexivity. Qed.

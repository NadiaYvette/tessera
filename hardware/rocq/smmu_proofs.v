(* Tessera — S4.4 (SMMUv3): the two-stage walk's compositional semantics.

   `machine.sail`'s `smmu_walk` (S4.4) models the SMMU's distinctive feature
   over the CPU MMU — a *two-stage* translation (SMMUv3 §3.3): stage-1
   (GVA → GPA, rooted at the context descriptor's stage-1 table) then stage-2
   (GPA → SPA, rooted at the stream table's stage-2 table), with the GPA
   zero-extended to a VA for the stage-2 input.  Both stages reuse the same
   Sv39 `translate`.

   This file proves the composition is what it says: the two-stage walk faults
   iff either stage faults, and on a two-stage hit it returns exactly the
   stage-2 (SPA, perm).  These are the compositional lemmas the SMMU coherence
   replay (unmap at stage-1 or stage-2 faults the two-stage walk) builds on.

   See doc/iommu-shootdown-plan.md (S4.4). *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import shootdown.      (* core_with_root *)
Import ListNotations.

(* Stage-1 faults ⇒ the two-stage walk faults. *)
Lemma smmu_walk_stage1_faults (s1_root s2_root : mword 44) (mem : list MemEntry) (gva : mword 64) :
  iommu_walk s1_root mem gva = None ->
  smmu_walk s1_root s2_root mem gva = None.
Proof.
  intros H. unfold smmu_walk, iommu_walk in *.
  rewrite H. reflexivity.
Qed.

(* Stage-1 hits but stage-2 faults ⇒ the two-stage walk faults. *)
Lemma smmu_walk_stage2_faults (s1_root s2_root : mword 44) (mem : list MemEntry) (gva : mword 64)
    (gpa : mword 56) (perm1 : Perm) :
  translate (core_with_root s1_root) mem gva = Some (gpa, perm1) ->
  iommu_walk s2_root mem (zero_extend gpa 64) = None ->
  smmu_walk s1_root s2_root mem gva = None.
Proof.
  intros H1 H2. unfold smmu_walk, iommu_walk, core_with_root in *.
  rewrite H1. cbn. exact H2.
Qed.

(* Both stages hit ⇒ the two-stage walk returns exactly the stage-2 (SPA, perm). *)
Lemma smmu_walk_spec (s1_root s2_root : mword 44) (mem : list MemEntry) (gva : mword 64)
    (gpa spa : mword 56) (perm1 perm : Perm) :
  translate (core_with_root s1_root) mem gva = Some (gpa, perm1) ->
  translate (core_with_root s2_root) mem (zero_extend gpa 64) = Some (spa, perm) ->
  smmu_walk s1_root s2_root mem gva = Some (spa, perm).
Proof.
  intros H1 H2. unfold smmu_walk, core_with_root in *.
  rewrite H1. cbn. exact H2.
Qed.

(* The empty table faults both stages. *)
Lemma test_vector_smmu_two_stage_empty_faults :
  smmu_walk (mword_of_int 1 : mword 44) (mword_of_int 2 : mword 44) []
            (mword_of_int 0 : mword 64) = None.
Proof. vm_compute. reflexivity. Qed.

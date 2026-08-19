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
Require Import coherence_leaf. (* unmap_leaf_mem *)
Require Import iommu_proofs.   (* iommu_unmap_faults *)
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

(* ============================================================
   S4.4 coherence replay: unmapping faults the two-stage walk.

   The SMMU coherence twin of iommu_proofs.iommu_unmap_faults: removing the
   leaf PTE for a GVA faults the two-stage walk.  Because the two stages are
   re-rooted independently (stage-1 at the CD's table, stage-2 at the STE's),
   unmapping at stage-1 faults the walk outright; unmapping at stage-2 faults
   it provided stage-1 still resolves to the same GPA (the alias-free
   "distinct tables" premise — otherwise the stage-2 unmap could disturb the
   stage-1 walk, which is exactly what wf_page_table rules out at the
   platform level).
   ============================================================ *)

(* Stage-1 unmap: the two-stage walk faults outright (stage-1 cannot reach the
   GPA to hand to stage-2). *)
Lemma smmu_unmap_stage1_faults (s1_root s2_root : mword 44) (mem : list MemEntry) (gva : mword 64) :
  smmu_walk s1_root s2_root (unmap_leaf_mem (core_with_root s1_root) mem gva) gva = None.
Proof.
  apply (smmu_walk_stage1_faults s1_root s2_root (unmap_leaf_mem (core_with_root s1_root) mem gva) gva).
  apply (iommu_unmap_faults s1_root mem gva).
Qed.

(* Stage-2 unmap: provided stage-1 still resolves to the same GPA after the
   stage-2 leaf removal (the stage-1 and stage-2 tables do not alias — the
   forest condition), stage-2 then faults and so does the composition. *)
Lemma smmu_unmap_stage2_faults (s1_root s2_root : mword 44) (mem : list MemEntry) (gva : mword 64)
    (gpa : mword 56) (perm1 : Perm) :
  translate (core_with_root s1_root)
    (unmap_leaf_mem (core_with_root s2_root) mem (zero_extend gpa 64)) gva = Some (gpa, perm1) ->
  smmu_walk s1_root s2_root (unmap_leaf_mem (core_with_root s2_root) mem (zero_extend gpa 64)) gva = None.
Proof.
  intros H1.
  apply (smmu_walk_stage2_faults s1_root s2_root
    (unmap_leaf_mem (core_with_root s2_root) mem (zero_extend gpa 64)) gva gpa perm1 H1).
  apply (iommu_unmap_faults s2_root mem (zero_extend gpa 64)).
Qed.

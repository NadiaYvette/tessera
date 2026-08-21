(* Tessera — SSG-4 / S4.5: Intel VT-d context selection and second-level walk.

   This is deliberately the first VT-d slice, not a claim to model the whole
   DMAR hardware.  A Requester ID indexes a context table; a present context
   selects a domain ID and a second-level page-table root.  The selected walk
   is the existing IOMMU/Sv39 walk, so the refinement and conformance boundary
   is explicit.  PASID first-stage translation, scalable-mode device tables,
   fault-recording, and queued invalidation are separate follow-ons.

   The abstraction matches VT-d 5.20 §3, §6.2, and §6.5: context selection is
   structural, while the second-level translation is the page-table walk.
*)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import conformance.
Require Import iommu_conformance.
Import ListNotations.

(* A present context selects exactly the IOMMU walk rooted at its SL root. *)
Lemma vtd_walk_context_spec (contexts : list VtdContext) (rid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_walk contexts rid mem iova = iommu_walk c.(VtdContext_sl_root) mem iova.
Proof.
  intros Hlookup Hpresent. unfold vtd_walk. rewrite Hlookup. cbn.
  rewrite Hpresent. reflexivity.
Qed.

(* A missing context entry is a translation fault. *)
Lemma vtd_walk_missing_context (contexts : list VtdContext) (rid : Z)
    (mem : list MemEntry) (iova : mword 64) :
  vtd_context_lookup contexts rid = None ->
  vtd_walk contexts rid mem iova = None.
Proof.
  intros H. unfold vtd_walk. rewrite H. reflexivity.
Qed.

(* A non-present context entry is a translation fault. *)
Lemma vtd_walk_nonpresent_context (contexts : list VtdContext) (rid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = false ->
  vtd_walk contexts rid mem iova = None.
Proof.
  intros Hlookup Hpresent. unfold vtd_walk. rewrite Hlookup. cbn.
  rewrite Hpresent. reflexivity.
Qed.

(* The VT-d walker is exactly the upstream oracle after context selection. *)
Definition oracle_vtd_walk (contexts : list VtdContext) (rid : Z)
    (mem : list MemEntry) (iova : mword 64)
    : option (mword 56 * Perm) :=
  match vtd_context_lookup contexts rid with
  | None => None
  | Some c =>
      if c.(VtdContext_present) then
        oracle_walk c.(VtdContext_sl_root) mem iova
      else None
  end.

Theorem vtd_walk_conforms (contexts : list VtdContext) (rid : Z)
    (mem : list MemEntry) (iova : mword 64) :
  vtd_walk contexts rid mem iova = oracle_vtd_walk contexts rid mem iova.
Proof.
  unfold vtd_walk, oracle_vtd_walk.
  destruct (vtd_context_lookup contexts rid) as [c|] eqn:H; [|reflexivity].
  destruct (c.(VtdContext_present)); [|reflexivity].
  rewrite (iommu_walk_translate_conforms c.(VtdContext_sl_root) mem iova).
  reflexivity.
Qed.

(* A VT-d context with the existing three-level hit table resolves to the same
   PA/permission as the direct IOMMU walk. *)
Definition vtd_hit_context : VtdContext :=
  {| VtdContext_present := true;
     VtdContext_did := 7;
     VtdContext_sl_root := root_ppn |}.

Lemma test_vector_vtd_context_hit :
  vtd_walk [vtd_hit_context] 0 table_ok va0 = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* A non-present context faults before touching the page table. *)
Definition vtd_nonpresent_context : VtdContext :=
  {| VtdContext_present := false;
     VtdContext_did := 7;
     VtdContext_sl_root := root_ppn |}.

Lemma test_vector_vtd_nonpresent_fault :
  vtd_walk [vtd_nonpresent_context] 0 table_ok va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* A missing Requester-ID context also faults. *)
Lemma test_vector_vtd_missing_context_fault :
  vtd_walk [] 0 table_ok va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* Conformance vector for an actual page-table fault through a present context. *)
Lemma test_vector_vtd_context_walk_fault :
  vtd_walk [vtd_hit_context] 0 [] va0 = None.
Proof. vm_compute. reflexivity. Qed.

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

(* ============================================================
   S4.5 first-stage / PASID slice: the two-stage walk.

   `vtd_walk_pasid` (machine.sail) resolves a present context (by Requester ID)
   and then a present PASID-table entry (by PASID), and runs the guest
   first-stage walk GVA -> GPA re-rooted at the entry's table, then the host
   second-level walk GPA -> SPA re-rooted at the context's SL root — exactly
   `iommu_walk` composed, so every IOMMU coherence/conformance result carries
   over (VT-d 5.20 §3 / §15, first-stage/second-stage translation).  This file
   proves the structural reduction to that composition, the per-stage fault and
   hit specifications, and the conformance oracle; the hypotheses are the
   S2.4/S4.2 weak-memory machine-ghost reification hand-off (the abstract
   "first-stage GPA" is the intermediate the ghost must witness).
   ============================================================ *)

(* With a present context and a present PASID entry, the two-stage walk is the
   composition of the entry's first-stage walk with the context's second-level
   walk (the GPA zero-extended to a VA for the second stage). *)
Lemma vtd_walk_pasid_two_stage (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (gva : mword 64) (c : VtdContext) (e : VtdPasid) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  vtd_walk_pasid contexts rid ptes pasid mem gva
  = match iommu_walk e.(VtdPasid_s1_root) mem gva with
    | None => None
    | Some (gpa, _) => iommu_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64)
    end.
Proof.
  intros Hc Hcp Hp Hpp.
  unfold vtd_walk_pasid.
  rewrite Hc, Hcp, Hp, Hpp. cbn. reflexivity.
Qed.

(* A missing context faults the PASID walk (no second-level root). *)
Lemma vtd_walk_pasid_missing_context (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (gva : mword 64) :
  vtd_context_lookup contexts rid = None ->
  vtd_walk_pasid contexts rid ptes pasid mem gva = None.
Proof.
  intros Hc. unfold vtd_walk_pasid. rewrite Hc. reflexivity.
Qed.

(* A non-present context faults (VT-d §3.3: only a present context translates). *)
Lemma vtd_walk_pasid_nonpresent_context (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (gva : mword 64) (c : VtdContext) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = false ->
  vtd_walk_pasid contexts rid ptes pasid mem gva = None.
Proof.
  intros Hc Hcp. unfold vtd_walk_pasid. rewrite Hc. cbn. rewrite Hcp. cbn. reflexivity.
Qed.

(* A missing PASID-table entry faults (VT-d §15.2: no first-stage structure). *)
Lemma vtd_walk_pasid_missing_pasid_entry (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (gva : mword 64) (c : VtdContext) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = None ->
  vtd_walk_pasid contexts rid ptes pasid mem gva = None.
Proof.
  intros Hc Hcp Hp. unfold vtd_walk_pasid. rewrite Hc, Hcp. cbn. rewrite Hp. cbn. reflexivity.
Qed.

(* A non-present PASID entry faults. *)
Lemma vtd_walk_pasid_nonpresent_pasid_entry (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (gva : mword 64) (c : VtdContext) (e : VtdPasid) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = false ->
  vtd_walk_pasid contexts rid ptes pasid mem gva = None.
Proof.
  intros Hc Hcp Hp Hpp. unfold vtd_walk_pasid. rewrite Hc, Hcp, Hp, Hpp. cbn. reflexivity.
Qed.

(* First-stage fault: the guest walk cannot resolve the GVA, so the two-stage
   walk faults outright (no GPA to hand to the second stage; VT-d §15.6). *)
Lemma vtd_walk_pasid_stage1_faults (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (gva : mword 64) (c : VtdContext) (e : VtdPasid) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  iommu_walk e.(VtdPasid_s1_root) mem gva = None ->
  vtd_walk_pasid contexts rid ptes pasid mem gva = None.
Proof.
  intros Hc Hcp Hp Hpp Hs1.
  rewrite (vtd_walk_pasid_two_stage contexts rid ptes pasid mem gva c e Hc Hcp Hp Hpp).
  rewrite Hs1. reflexivity.
Qed.

(* First stage hits but the second stage faults: the two-stage walk faults. *)
Lemma vtd_walk_pasid_stage2_faults (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (gva : mword 64) (c : VtdContext) (e : VtdPasid)
    (gpa : mword 56) (perm1 : Perm) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  iommu_walk e.(VtdPasid_s1_root) mem gva = Some (gpa, perm1) ->
  iommu_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64) = None ->
  vtd_walk_pasid contexts rid ptes pasid mem gva = None.
Proof.
  intros Hc Hcp Hp Hpp Hs1 Hs2.
  rewrite (vtd_walk_pasid_two_stage contexts rid ptes pasid mem gva c e Hc Hcp Hp Hpp).
  rewrite Hs1. cbn. exact Hs2.
Qed.

(* Both stages hit: the two-stage walk returns exactly the second-stage (SPA, perm). *)
Lemma vtd_walk_pasid_spec (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (gva : mword 64) (c : VtdContext) (e : VtdPasid)
    (gpa spa : mword 56) (perm1 perm : Perm) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  iommu_walk e.(VtdPasid_s1_root) mem gva = Some (gpa, perm1) ->
  iommu_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64) = Some (spa, perm) ->
  vtd_walk_pasid contexts rid ptes pasid mem gva = Some (spa, perm).
Proof.
  intros Hc Hcp Hp Hpp Hs1 Hs2.
  rewrite (vtd_walk_pasid_two_stage contexts rid ptes pasid mem gva c e Hc Hcp Hp Hpp).
  rewrite Hs1. cbn. exact Hs2.
Qed.

(* The VT-d PASID walker agrees with the upstream Sv39 oracle exactly: each
   stage is `iommu_walk`, so `iommu_walk_translate_conforms` (G1, via the IOMMU
   walker) transfers stage-by-stage after the structural lookup. *)
Definition oracle_vtd_walk_pasid (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) : option (mword 56 * Perm) :=
  match vtd_context_lookup contexts rid with
  | None => None
  | Some c =>
      if c.(VtdContext_present) then
        match vtd_pasid_lookup ptes pasid with
        | None => None
        | Some e =>
            if e.(VtdPasid_present) then
              match oracle_walk e.(VtdPasid_s1_root) mem iova with
              | None => None
              | Some (gpa, _) => oracle_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64)
              end
            else None
        end
      else None
  end.

Theorem vtd_walk_pasid_conforms (contexts : list VtdContext) (rid : Z) (ptes : list VtdPasid) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) :
  vtd_walk_pasid contexts rid ptes pasid mem iova =
  oracle_vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  unfold vtd_walk_pasid, oracle_vtd_walk_pasid.
  destruct (vtd_context_lookup contexts rid) as [c|] eqn:Hc; [|reflexivity].
  cbn. destruct (c.(VtdContext_present)) eqn:Hcp; [|reflexivity].
  cbn. destruct (vtd_pasid_lookup ptes pasid) as [e|] eqn:He; [|reflexivity].
  cbn. destruct (e.(VtdPasid_present)) eqn:Hpp; [|reflexivity].
  cbn.
  rewrite (iommu_walk_translate_conforms e.(VtdPasid_s1_root) mem iova).
  destruct (oracle_walk e.(VtdPasid_s1_root) mem iova) as [[gpa perm1]|] eqn:Hg; [|reflexivity].
  rewrite (iommu_walk_translate_conforms c.(VtdContext_sl_root) mem (zero_extend gpa 64)).
  reflexivity.
Qed.

(* ----------------------------------------------------------------------
   Executable vectors: a full two-stage HIT through a present PASID entry, and
   each structural/fault case, pinned against VT-d §15 (first-stage guest
   translation + second-level).
   ---------------------------------------------------------------------- *)

(* Distinct roots so the first-stage (guest) and second-level (host) tables do
   not alias in the shared mem.  Stage-1 maps GVA va0 -> GPA 0 (leaf ppn 0);
   stage-2 maps the zero-extended GPA (= va0) -> SPA [expected_pa]. *)
Definition vtd_s1_root : mword 44 := mword_of_int 11.
Definition vtd_s1_mid  : mword 44 := mword_of_int 12.
Definition vtd_s1_leaf : mword 44 := mword_of_int 13.
Definition vtd_s2_root : mword 44 := mword_of_int 21.
Definition vtd_s2_mid  : mword 44 := mword_of_int 22.
Definition vtd_s2_leaf : mword 44 := mword_of_int 23.

Definition table_vtd_s1_gpa0 : PageTable :=
  [ {| MemEntry_addr := pte_address vtd_s1_root (vpn2 va0); MemEntry_pte := ptr_pte vtd_s1_mid |};
    {| MemEntry_addr := pte_address vtd_s1_mid  (vpn1 va0); MemEntry_pte := ptr_pte vtd_s1_leaf |};
    {| MemEntry_addr := pte_address vtd_s1_leaf (vpn0 va0); MemEntry_pte := ro_pte (mword_of_int 0 : mword 44) |} ].

Definition table_vtd_s2_spa : PageTable :=
  [ {| MemEntry_addr := pte_address vtd_s2_root (vpn2 va0); MemEntry_pte := ptr_pte vtd_s2_mid |};
    {| MemEntry_addr := pte_address vtd_s2_mid  (vpn1 va0); MemEntry_pte := ptr_pte vtd_s2_leaf |};
    {| MemEntry_addr := pte_address vtd_s2_leaf (vpn0 va0); MemEntry_pte := ro_pte leaf_ppn |} ].

Definition mem_vtd_pasid_hit : PageTable := List.app table_vtd_s1_gpa0 table_vtd_s2_spa.

(* A present context whose SL root is the stage-2 table, with a present PASID
   entry whose first-stage root is the guest table. *)
Definition vtd_pasid_hit_context : VtdContext :=
  {| VtdContext_present := true; VtdContext_did := 7; VtdContext_sl_root := vtd_s2_root |}.
Definition vtd_pasid_hit_entry : VtdPasid :=
  {| VtdPasid_present := true; VtdPasid_s1_root := vtd_s1_root |}.

Lemma test_vector_vtd_pasid_two_stage_hit :
  vtd_walk_pasid [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry] 0 mem_vtd_pasid_hit va0 = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* A missing PASID entry faults even when the context is present. *)
Lemma test_vector_vtd_pasid_missing_fault :
  vtd_walk_pasid [vtd_pasid_hit_context] 0 [] 0 mem_vtd_pasid_hit va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* A non-present PASID entry faults. *)
Definition vtd_pasid_nonpresent_entry : VtdPasid :=
  {| VtdPasid_present := false; VtdPasid_s1_root := vtd_s1_root |}.

Lemma test_vector_vtd_pasid_nonpresent_fault :
  vtd_walk_pasid [vtd_pasid_hit_context] 0 [vtd_pasid_nonpresent_entry] 0 mem_vtd_pasid_hit va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* A non-present context faults the PASID walk before the PASID lookup. *)
Lemma test_vector_vtd_pasid_nonpresent_context_fault :
  vtd_walk_pasid [vtd_nonpresent_context] 0 [vtd_pasid_hit_entry] 0 mem_vtd_pasid_hit va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* A present context + PASID entry, but an empty page table: both stages fault. *)
Lemma test_vector_vtd_pasid_empty_fault :
  vtd_walk_pasid [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry] 0 [] va0 = None.
Proof. vm_compute. reflexivity. Qed.

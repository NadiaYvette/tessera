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
From Stdlib Require Import Lia.
Require Import machine_types.
Require Import machine.
Require Import machine_encoding. (* invalid_pte *)
Require Import shootdown.        (* core_with_root *)
Require Import coherence_leaf.   (* invalidate_leaf_mem *)
Require Import conformance.
Require Import iommu_conformance.
Require Import iommu_proofs.     (* iommu_shootdown_via_queue (+_mem), iommu_invalidate_faults *)
Require Import intc_types.       (* Intc (SSG-3) for FRCD interrupt delivery *)
Require Import intc.             (* intc_send / intc_ack *)
Require Import intc_proofs.      (* intc_send_sets_pending, intc_ack_unmasked_rings, preserves *)
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

(* ============================================================
   S4.5 PASID-cache slice: the cached first-stage lookup is coherent with the
   PASID table, so the cached two-stage walk equals the table-driven one.
   ============================================================ *)

(* The cached two-stage walk reduces to the same iommu_walk composition as
   `vtd_walk_pasid`, with the cache entry's root standing in for the table's. *)
Lemma pasid_cached_walk_two_stage (contexts : list VtdContext) (rid : Z)
    (cache : list PasidCacheEntry) (pasid : Z) (mem : list MemEntry) (gva : mword 64)
    (c : VtdContext) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  pasid_cache_lookup cache pasid = Some ec ->
  ec.(PasidCacheEntry_present) = true ->
  pasid_cached_walk contexts rid cache pasid mem gva
  = match iommu_walk ec.(PasidCacheEntry_s1_root) mem gva with
    | None => None
    | Some (gpa, _) => iommu_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64)
    end.
Proof.
  intros Hc Hcp Hcl Hcpp.
  unfold pasid_cached_walk.
  rewrite Hc, Hcp, Hcl, Hcpp. cbn. reflexivity.
Qed.

(* A cached entry whose first-stage root matches the table's makes the cached
   walk agree with `vtd_walk_pasid` — the cache is an alias for the table. *)
Lemma pasid_cached_walk_of_table (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) (e : VtdPasid) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  pasid_cache_lookup cache pasid = Some ec ->
  ec.(PasidCacheEntry_present) = true ->
  ec.(PasidCacheEntry_s1_root) = e.(VtdPasid_s1_root) ->
  pasid_cached_walk contexts rid cache pasid mem iova =
  vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hc Hcp Hp Hpp Hcl Hcpp Hs1root.
  rewrite (pasid_cached_walk_two_stage contexts rid cache pasid mem iova c ec Hc Hcp Hcl Hcpp).
  rewrite (vtd_walk_pasid_two_stage contexts rid ptes pasid mem iova c e Hc Hcp Hp Hpp).
  rewrite Hs1root. reflexivity.
Qed.

(* The PASID cache is coherent with the PASID table for (rid, pasid): when both
   walks resolve a present context + present table entry, the cached entry is
   present and holds the table's first-stage root. *)
Definition pasid_cache_coherent (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z) : Prop :=
  match (vtd_context_lookup contexts rid, vtd_pasid_lookup ptes pasid, pasid_cache_lookup cache pasid) with
  | (Some c, Some e, Some ec) =>
      c.(VtdContext_present) = true -> e.(VtdPasid_present) = true ->
      ec.(PasidCacheEntry_present) = true /\
      ec.(PasidCacheEntry_pasid) = pasid /\
      ec.(PasidCacheEntry_s1_root) = e.(VtdPasid_s1_root)
  | _ => True
  end.

(* A coherent cache makes the cached walk equal the table-driven two-stage
   walk — the analogue of `iotlb_coherent` (IOTLB ⊆ mapping) for the first
   stage, so every `vtd_walk_pasid` result transfers to the cache. *)
Theorem pasid_cached_walk_coherent (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) (e : VtdPasid) (ec : PasidCacheEntry) :
  pasid_cache_coherent contexts rid ptes cache pasid ->
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  pasid_cache_lookup cache pasid = Some ec ->
  pasid_cached_walk contexts rid cache pasid mem iova =
  vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hcoh Hc Hcp Hp Hpp Hcl.
  unfold pasid_cache_coherent in Hcoh.
  rewrite Hc, Hp, Hcl in Hcoh. cbn in Hcoh.
  specialize (Hcoh Hcp). specialize (Hcoh Hpp).
  destruct Hcoh as [Hcpp [Hpasid Hs1root]].
  apply (pasid_cached_walk_of_table contexts rid ptes cache pasid mem iova c e ec
            Hc Hcp Hp Hpp Hcl Hcpp Hs1root).
Qed.

(* Executable vector: a coherent cache entry makes the cached walk resolve to
   the same SPA as the table-driven two-stage walk. *)
Definition vtd_coherent_cache_entry : PasidCacheEntry :=
  {| PasidCacheEntry_present := true; PasidCacheEntry_pasid := 0; PasidCacheEntry_s1_root := vtd_s1_root |}.

Lemma test_vector_vtd_pasid_cache_coherent :
  pasid_cached_walk [vtd_pasid_hit_context] 0 [vtd_coherent_cache_entry] 0 mem_vtd_pasid_hit va0
  = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.5 fault-recording slice: on a translation fault a record (requester ID,
   PASID, IOVA, reason) is produced — a record exactly when the walk faults.
   ============================================================ *)

(* Stage-1 fault records FR_Stage1Fault. *)
Lemma vtd_record_fault_stage1_spec (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (pasid : Z) (mem : list MemEntry) (gva : mword 64)
    (c : VtdContext) (e : VtdPasid) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  iommu_walk e.(VtdPasid_s1_root) mem gva = None ->
  vtd_record_fault contexts rid ptes pasid mem gva
  = Some {| FaultRecord_did := rid; FaultRecord_pasid := pasid;
            FaultRecord_iova := gva; FaultRecord_reason := FR_Stage1Fault |}.
Proof.
  intros Hc Hcp Hp Hpp Hs1.
  unfold vtd_record_fault. rewrite Hc, Hcp, Hp, Hpp. cbn. rewrite Hs1. reflexivity.
Qed.

(* Stage-2 fault (stage-1 resolved to a GPA) records FR_Stage2Fault for the
   freed frame. *)
Lemma vtd_record_fault_stage2_spec (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (pasid : Z) (mem : list MemEntry) (gva : mword 64)
    (c : VtdContext) (e : VtdPasid) (gpa : mword 56) (perm1 : Perm) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  iommu_walk e.(VtdPasid_s1_root) mem gva = Some (gpa, perm1) ->
  iommu_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64) = None ->
  vtd_record_fault contexts rid ptes pasid mem gva
  = Some {| FaultRecord_did := rid; FaultRecord_pasid := pasid;
            FaultRecord_iova := gva; FaultRecord_reason := FR_Stage2Fault |}.
Proof.
  intros Hc Hcp Hp Hpp Hs1 Hs2.
  unfold vtd_record_fault. rewrite Hc, Hcp, Hp, Hpp. cbn. rewrite Hs1. cbn. rewrite Hs2. reflexivity.
Qed.

(* A resolving translation records nothing (no spurious fault). *)
Lemma vtd_record_fault_hit_none (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (pasid : Z) (mem : list MemEntry) (gva : mword 64)
    (c : VtdContext) (e : VtdPasid) (gpa spa : mword 56) (perm1 perm : Perm) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  iommu_walk e.(VtdPasid_s1_root) mem gva = Some (gpa, perm1) ->
  iommu_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64) = Some (spa, perm) ->
  vtd_record_fault contexts rid ptes pasid mem gva = None.
Proof.
  intros Hc Hcp Hp Hpp Hs1 Hs2.
  unfold vtd_record_fault. rewrite Hc, Hcp, Hp, Hpp. cbn. rewrite Hs1. cbn. rewrite Hs2. reflexivity.
Qed.

(* A fault is recorded iff the two-stage walk faults.  `vtd_record_fault` and
   `vtd_walk_pasid` are structurally identical (same lookups, same present
   checks, same two stages), so destroying the shared sub-terms rewrites both
   in the goal and the two boolean-intention sides reduce in lockstep. *)
Lemma vtd_record_fault_iff_walk (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (pasid : Z) (mem : list MemEntry) (iova : mword 64) :
  (match vtd_record_fault contexts rid ptes pasid mem iova with
   | None => False | Some _ => True end)
  = (match vtd_walk_pasid contexts rid ptes pasid mem iova with
     | None => True | Some _ => False end).
Proof.
  unfold vtd_record_fault, vtd_walk_pasid.
  destruct (vtd_context_lookup contexts rid) as [c|]; [|reflexivity]. cbn.
  destruct (c.(VtdContext_present)); [|reflexivity]. cbn.
  destruct (vtd_pasid_lookup ptes pasid) as [e|]; [|reflexivity]. cbn.
  destruct (e.(VtdPasid_present)); [|reflexivity]. cbn.
  destruct (iommu_walk e.(VtdPasid_s1_root) mem iova) as [[gpa perm1]|]; [|reflexivity]. cbn.
  destruct (iommu_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64)) as [|[_ _]];
    [|reflexivity]. reflexivity.
Qed.

(* Executable vectors: empty tables record a stage-1 fault; a missing context
   records the context-missing fault; a resolving translation records nothing. *)
Lemma test_vector_vtd_record_fault_stage1 :
  vtd_record_fault [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry] 0 [] va0
  = Some {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := va0;
            FaultRecord_reason := FR_Stage1Fault |}.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_vtd_record_fault_missing_context :
  vtd_record_fault [] 0 [vtd_pasid_hit_entry] 0 mem_vtd_pasid_hit va0
  = Some {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := va0;
            FaultRecord_reason := FR_ContextMissing |}.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_vtd_record_fault_hit_none :
  vtd_record_fault [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry] 0 mem_vtd_pasid_hit va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.5 PASID in the machine ghost: after the queue shootdown un-maps the freed
   frame at the context's SL root and invalidates the IOTLB, the two-stage PASID
   walk faults for that frame and a fault is recorded — provided the guest
   first stage still resolves it (the alias-free distinct-tables premise) and
   the freed frame's GPA zero-extends back to the same VA.
   ============================================================ *)

(* The machine-ghost post-state (iommu_shootdown_via_queue's break-before-make
   mem) makes the VT-d two-stage walk fault for the freed frame, with the fault
   recorded.  The four hypotheses on the top capture the structural resolution
   and the alias-free / GPA=VA premises. *)
Theorem vtd_shootdown_via_queue_pasid_faults (m : Machine) (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (pasid : Z) (c : VtdContext) (e : VtdPasid)
    (root : mword 44) (va : mword 64) (p : Pte) (gpa : mword 56) (perm1 : Perm) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  c.(VtdContext_sl_root) = root ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  e.(VtdPasid_s1_root) <> root ->
  p.(Pte_valid) = false ->
  iommu_walk e.(VtdPasid_s1_root)
    (Machine_mem (iommu_shootdown_via_queue m root va p)) va = Some (gpa, perm1) ->
  zero_extend gpa 64 = va ->
  vtd_walk_pasid contexts rid ptes pasid
    (Machine_mem (iommu_shootdown_via_queue m root va p)) va = None /\
  vtd_record_fault contexts rid ptes pasid
    (Machine_mem (iommu_shootdown_via_queue m root va p)) va <> None.
Proof.
  intros Hc Hcp Hroot Hp Hpp Hdiff Hinv Hs1 Hze.
  split.
  -    rewrite (vtd_walk_pasid_two_stage contexts rid ptes pasid
               (Machine_mem (iommu_shootdown_via_queue m root va p)) va
               c e Hc Hcp Hp Hpp).
    rewrite Hs1. simpl.
    rewrite Hroot. rewrite Hze.
    apply (iommu_invalidate_faults root m.(Machine_mem) va p Hinv).
  - assert (Hrec : vtd_record_fault contexts rid ptes pasid
                     (Machine_mem (iommu_shootdown_via_queue m root va p)) va
                     = Some {| FaultRecord_did := rid; FaultRecord_pasid := pasid;
                              FaultRecord_iova := va; FaultRecord_reason := FR_Stage2Fault |}).
    { apply (vtd_record_fault_stage2_spec contexts rid ptes pasid
               (Machine_mem (iommu_shootdown_via_queue m root va p)) va
               c e gpa perm1 Hc Hcp Hp Hpp Hs1).
      rewrite Hroot. rewrite Hze.
      rewrite (iommu_shootdown_via_queue_mem m root va p).
      apply (iommu_invalidate_faults root m.(Machine_mem) va p Hinv). }
    rewrite Hrec. discriminate.
Qed.

(* A machine whose mem is the two-stage hit tables, sharing the context's SL
   root. *)
Definition vtd_shoot_m : Machine :=
  {| Machine_mem := mem_vtd_pasid_hit; Machine_cores := []; Machine_ram := [];
     Machine_ipi := []; Machine_iotlb := []; Machine_devtlbs := [];
     Machine_prireqs := []; Machine_ioqueue := []; Machine_stes := []; Machine_cds := [] |}.

(* After the shootdown at the context's SL root, the freed frame's two-stage
   walk faults. *)
Lemma test_vector_vtd_shootdown_pasid :
  vtd_walk_pasid [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry] 0
    (Machine_mem (iommu_shootdown_via_queue vtd_shoot_m vtd_s2_root va0 invalid_pte)) va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* ... and the fault is recorded (FR_Stage2Fault) for the freed frame. *)
Lemma test_vector_vtd_shootdown_pasid_record :
  vtd_record_fault [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry] 0
    (Machine_mem (iommu_shootdown_via_queue vtd_shoot_m vtd_s2_root va0 invalid_pte)) va0
  = Some {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := va0;
            FaultRecord_reason := FR_Stage2Fault |}.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.5 PASID-cache eviction / refill: invalidation clears the cached
   first-stage root for a PASID (the slot turns non-present, so the cached
   walk misses), and refill re-installs the table's root (so the cached walk
   equals the table walk again).  Eviction breaks `pasid_cache_coherent`;
   refill restores it — the miss/refill cycle a translation after
   invalidation must go through.
   ============================================================ *)

(* Eviction clears the evicted PASID's slot: the lookup afterwards returns a
   non-present entry — the cache-miss state. *)
Lemma pasid_cache_evict_lookup (cache : list PasidCacheEntry) (pasid : Z) (ec : PasidCacheEntry) :
  pasid_cache_lookup cache pasid = Some ec ->
  exists ec', pasid_cache_lookup (pasid_cache_evict cache pasid) pasid = Some ec' /\
             ec'.(PasidCacheEntry_present) = false.
Proof.
  revert pasid ec. induction cache as [| e rest IH]; cbn.
  - intros; discriminate.
  - intros [|p|p] ec H; cbn in H.
    + exists {| PasidCacheEntry_present := false; PasidCacheEntry_pasid := e.(PasidCacheEntry_pasid);
               PasidCacheEntry_s1_root := e.(PasidCacheEntry_s1_root) |}.
      cbn. split; reflexivity.
    + apply (IH (Z.pos p - 1) ec). exact H.
    + apply (IH (Z.neg p - 1) ec). exact H.
Qed.

(* The evicted PASID's cached walk misses: the slot is non-present, so the
   cached two-stage walk faults — the IOMMU must re-walk the PASID table. *)
Lemma pasid_cached_walk_evict_misses (contexts : list VtdContext) (rid : Z)
    (cache : list PasidCacheEntry) (pasid : Z) (mem : list MemEntry) (iova : mword 64)
    (c : VtdContext) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  pasid_cache_lookup cache pasid = Some ec ->
  pasid_cached_walk contexts rid (pasid_cache_evict cache pasid) pasid mem iova = None.
Proof.
  intros Hc Hcp Hcl.
  destruct (pasid_cache_evict_lookup cache pasid ec Hcl) as [ec' [Hcl' Hp']].
  unfold pasid_cached_walk. rewrite Hc, Hcp, Hcl'. cbn. rewrite Hp'. cbn. reflexivity.
Qed.

(* Eviction is selective: lookups for any other PASID are untouched. *)
Lemma pasid_cache_evict_preserves_other (cache : list PasidCacheEntry) (pasid pasid' : Z) :
  pasid <> pasid' ->
  forall e, pasid_cache_lookup cache pasid' = Some e ->
         pasid_cache_lookup (pasid_cache_evict cache pasid) pasid' = Some e.
Proof.
  revert pasid pasid'. induction cache as [| hd rest IH]; cbn.
  - intros; discriminate.
  - intros [|p|p] [|q|q] Hneq e H.
    + exfalso. apply Hneq. reflexivity.
    + cbn in H. exact H.
    + cbn in H. exact H.
    + cbn in H. exact H.
    + apply (IH (Z.pos p - 1) (Z.pos q - 1)); [intros Hsub; apply Hneq; lia | cbn in H; exact H].
    + apply (IH (Z.pos p - 1) (Z.neg q - 1)); [intros Hsub; apply Hneq; lia | cbn in H; exact H].
    + cbn in H. exact H.
    + apply (IH (Z.neg p - 1) (Z.pos q - 1)); [intros Hsub; apply Hneq; lia | cbn in H; exact H].
    + apply (IH (Z.neg p - 1) (Z.neg q - 1)); [intros Hsub; apply Hneq; lia | cbn in H; exact H].
Qed.

(* Refill re-installs the evicted slot as present with the given root. *)
Lemma pasid_cache_refill_lookup (cache : list PasidCacheEntry) (pasid : Z) (root : mword 44)
    (ec : PasidCacheEntry) :
  pasid_cache_lookup cache pasid = Some ec ->
  exists ec', pasid_cache_lookup (pasid_cache_refill cache pasid root) pasid = Some ec' /\
             ec'.(PasidCacheEntry_present) = true /\
             ec'.(PasidCacheEntry_s1_root) = root.
Proof.
  revert pasid ec. induction cache as [| e rest IH]; cbn.
  - intros; discriminate.
  - intros [|p|p] ec H; cbn in H.
    + exists {| PasidCacheEntry_present := true; PasidCacheEntry_pasid := 0;
               PasidCacheEntry_s1_root := root |}.
      cbn. repeat split; reflexivity.
    + apply (IH (Z.pos p - 1) ec). exact H.
    + apply (IH (Z.neg p - 1) ec). exact H.
Qed.

(* A refilled slot holding the table's first-stage root makes the cached walk
   agree with the table-driven two-stage walk again — coherence restored. *)
Lemma pasid_cache_refill_coherent (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) (e : VtdPasid) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  pasid_cache_lookup cache pasid = Some ec ->
  pasid_cached_walk contexts rid (pasid_cache_refill cache pasid e.(VtdPasid_s1_root)) pasid mem iova
  = vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hc Hcp Hp Hpp Hcl.
  destruct (pasid_cache_refill_lookup cache pasid e.(VtdPasid_s1_root) ec Hcl) as [ec' [Hcl' [Hp' Hs]]].
  apply (pasid_cached_walk_of_table contexts rid ptes (pasid_cache_refill cache pasid e.(VtdPasid_s1_root))
           pasid mem iova c e ec' Hc Hcp Hp Hpp Hcl' Hp' Hs).
Qed.

(* The evict → refill cycle: eviction breaks the cached walk for the PASID
   (a miss), and refilling with the table's root restores the table-driven
   result — the invalidation-then-retranslate cycle in one theorem. *)
Theorem pasid_cache_evict_refill_cycle (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) (e : VtdPasid) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  pasid_cache_lookup cache pasid = Some ec ->
  pasid_cached_walk contexts rid (pasid_cache_evict cache pasid) pasid mem iova = None /\
  pasid_cached_walk contexts rid (pasid_cache_refill (pasid_cache_evict cache pasid) pasid
                                    e.(VtdPasid_s1_root)) pasid mem iova
  = vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hc Hcp Hp Hpp Hcl.
  destruct (pasid_cache_evict_lookup cache pasid ec Hcl) as [ec' [Hev Hpev]].
  split.
  - apply (pasid_cached_walk_evict_misses contexts rid cache pasid mem iova c ec Hc Hcp Hcl).
  - apply (pasid_cache_refill_coherent contexts rid ptes (pasid_cache_evict cache pasid) pasid
             mem iova c e ec' Hc Hcp Hp Hpp Hev).
Qed.

(* Executable vector: evicting PASID 0 turns the cached walk into a miss. *)
Lemma test_vector_vtd_pasid_cache_evict :
  pasid_cached_walk [vtd_pasid_hit_context] 0
    (pasid_cache_evict [vtd_coherent_cache_entry] 0) 0 mem_vtd_pasid_hit va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.5 scalable-mode device table: the requester-ID-indexed device table
   (DTE) selects the context for the second-level walk; `vtd_walk_device`
   reduces to the context's SL walk, and agrees with the flat `vtd_walk`
   exactly when the DTE points at the context the flat lookup would find.
   ============================================================ *)

(* The device-table walk reduces to the selected context's second-level walk. *)
Lemma vtd_walk_device_two_stage (devtbl : list VtdDeviceEntry) (contexts : list VtdContext)
    (rid : Z) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) (c : VtdContext) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  vtd_context_lookup contexts d.(VtdDeviceEntry_ctx_index) = Some c ->
  c.(VtdContext_present) = true ->
  vtd_walk_device devtbl contexts rid mem iova = iommu_walk c.(VtdContext_sl_root) mem iova.
Proof.
  intros Hd Hdp Hc Hcp.
  unfold vtd_walk_device. rewrite Hd, Hdp, Hc, Hcp. cbn. reflexivity.
Qed.

(* The DTE for rid selecting the context the flat lookup finds makes the
   device-table walk agree with `vtd_walk` — the two views of the same
   context selection. *)
Lemma vtd_walk_device_of_context (devtbl : list VtdDeviceEntry) (contexts : list VtdContext)
    (rid : Z) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) (c : VtdContext) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  d.(VtdDeviceEntry_ctx_index) = rid ->
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_walk_device devtbl contexts rid mem iova = vtd_walk contexts rid mem iova.
Proof.
  intros Hd Hdp Hidx Hc Hcp.
  unfold vtd_walk_device, vtd_walk.
  rewrite Hd, Hdp. rewrite Hidx in *. rewrite Hc, Hcp. cbn. reflexivity.
Qed.

(* Faults: a missing DTE, a non-present DTE, a missing context, and a
   non-present context each fault the device-table walk. *)
Lemma vtd_walk_device_missing_fault (contexts : list VtdContext) (rid : Z) (mem : list MemEntry) (iova : mword 64) :
  vtd_walk_device [] contexts rid mem iova = None.
Proof. unfold vtd_walk_device. cbn. reflexivity. Qed.

Lemma vtd_walk_device_nonpresent_fault (devtbl : list VtdDeviceEntry) (contexts : list VtdContext)
    (rid : Z) (mem : list MemEntry) (iova : mword 64) (d : VtdDeviceEntry) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = false ->
  vtd_walk_device devtbl contexts rid mem iova = None.
Proof. intros Hd Hdp. unfold vtd_walk_device. rewrite Hd, Hdp. cbn. reflexivity. Qed.

Lemma vtd_walk_device_missing_context_fault (devtbl : list VtdDeviceEntry) (contexts : list VtdContext)
    (rid : Z) (mem : list MemEntry) (iova : mword 64) (d : VtdDeviceEntry) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  vtd_context_lookup contexts d.(VtdDeviceEntry_ctx_index) = None ->
  vtd_walk_device devtbl contexts rid mem iova = None.
Proof. intros Hd Hdp Hc. unfold vtd_walk_device. rewrite Hd, Hdp, Hc. cbn. reflexivity. Qed.

Lemma vtd_walk_device_nonpresent_context_fault (devtbl : list VtdDeviceEntry) (contexts : list VtdContext)
    (rid : Z) (mem : list MemEntry) (iova : mword 64) (d : VtdDeviceEntry) (c : VtdContext) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  vtd_context_lookup contexts d.(VtdDeviceEntry_ctx_index) = Some c ->
  c.(VtdContext_present) = false ->
  vtd_walk_device devtbl contexts rid mem iova = None.
Proof. intros Hd Hdp Hc Hcp. unfold vtd_walk_device. rewrite Hd, Hdp, Hc, Hcp. cbn. reflexivity. Qed.

(* Executable vector: a present DTE for rid 0 selecting the hit context
   resolves the second-level walk to the same SPA as the direct walk. *)
Definition vtd_dev_hit_entry : VtdDeviceEntry :=
  {| VtdDeviceEntry_present := true; VtdDeviceEntry_did := 7; VtdDeviceEntry_ctx_index := 0;
     VtdDeviceEntry_pasid_tbl := 0 |}.

Lemma test_vector_vtd_walk_device_hit :
  vtd_walk_device [vtd_dev_hit_entry] [vtd_pasid_hit_context] 0 mem_vtd_pasid_hit va0 = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.5 FRCD + fault-message signalling: a fault is recorded as an FRCD entry
   (DID, PASID, IOVA, reason), the FRCD raises the interrupt line, and the
   fault message carries the DID+PASID of the faulting endpoint.
   ============================================================ *)

(* The FaultRecord → FrcdEntry transcription. *)
Definition frcd_of (fr : FaultRecord) : FrcdEntry :=
  {| FrcdEntry_did := FaultRecord_did fr; FrcdEntry_pasid := FaultRecord_pasid fr;
     FrcdEntry_iova := FaultRecord_iova fr; FrcdEntry_reason := FaultRecord_reason fr |}.

(* Recording a fault makes it findable in the FRCD, keyed by (did, pasid, iova).
   (The Sail model carries the (did, pasid) key as a pair to dodge a Sail
   rocq-backend quirk with two unchanged int recursion args; the pair is
   destructured in the guard, so the proofs see the two ints directly.) *)
Lemma frcd_record_adds (fr : FaultRecord) (cache : list FrcdEntry) :
  frcd_lookup (frcd_record fr cache) (FaultRecord_did fr, FaultRecord_pasid fr) (FaultRecord_iova fr)
  = Some (frcd_of fr).
Proof.
  cbn.
  rewrite (proj2 (Z.eqb_eq (FaultRecord_did fr) (FaultRecord_did fr)) eq_refl).
  rewrite (proj2 (Z.eqb_eq (FaultRecord_pasid fr) (FaultRecord_pasid fr)) eq_refl).
  rewrite (proj2 (eq_vec_true_iff (FaultRecord_iova fr) (FaultRecord_iova fr)) eq_refl).
  cbn. reflexivity.
Qed.

(* Recording never loses a prior fault for a *different* endpoint/address
   (the new record only shadows an entry with the same did+pasid+iova). *)
Lemma frcd_record_preserves (fr : FaultRecord) (cache : list FrcdEntry) (did pasid : Z) (iova : mword 64) (e : FrcdEntry) :
  (did <> FaultRecord_did fr \/ pasid <> FaultRecord_pasid fr \/ iova <> FaultRecord_iova fr) ->
  frcd_lookup cache (did, pasid) iova = Some e ->
  frcd_lookup (frcd_record fr cache) (did, pasid) iova = Some e.
Proof.
  intros [Hd | [Hp | Hi]] Hlook.
  - cbn. destruct (Z.eqb (FaultRecord_did fr) did) eqn:E.
    + exfalso. apply Hd. apply Z.eqb_eq in E. exact (eq_sym E).
    + cbn. exact Hlook.
  - cbn. destruct (Z.eqb (FaultRecord_pasid fr) pasid) eqn:E.
    + exfalso. apply Hp. apply Z.eqb_eq in E. exact (eq_sym E).
    + cbn. rewrite Bool.andb_false_r. cbn. exact Hlook.
  - cbn. destruct (eq_vec (FaultRecord_iova fr) iova) eqn:E.
    + exfalso. apply Hi. apply eq_vec_true_iff in E. exact (eq_sym E).
    + cbn. rewrite Bool.andb_false_r. cbn. rewrite Bool.andb_false_r. cbn. exact Hlook.
Qed.

(* The interrupt line: any recorded fault makes the FRCD pending. *)
Lemma frcd_record_signals (fr : FaultRecord) (cache : list FrcdEntry) :
  frcd_pending (frcd_record fr cache) = true.
Proof. cbn. reflexivity. Qed.

(* The fault message carries the DID + PASID of the faulting endpoint. *)
Lemma fault_msg_of_record (fr : FaultRecord) :
  fault_msg_did_pasid (frcd_of fr) = (FaultRecord_did fr, FaultRecord_pasid fr).
Proof. cbn. reflexivity. Qed.

(* After the queue shootdown of the freed frame, the fault is recorded, the
   FRCD raises the interrupt, and the fault message carries (rid, pasid). *)
Theorem vtd_shootdown_frcd_pending (m : Machine) (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (pasid : Z) (c : VtdContext) (e : VtdPasid)
    (root : mword 44) (va : mword 64) (p : Pte) (gpa : mword 56) (perm1 : Perm) (fr : FaultRecord) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  c.(VtdContext_sl_root) = root ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  e.(VtdPasid_s1_root) <> root ->
  p.(Pte_valid) = false ->
  iommu_walk e.(VtdPasid_s1_root) (Machine_mem (iommu_shootdown_via_queue m root va p)) va = Some (gpa, perm1) ->
  zero_extend gpa 64 = va ->
  vtd_record_fault contexts rid ptes pasid (Machine_mem (iommu_shootdown_via_queue m root va p)) va = Some fr ->
  frcd_pending (frcd_record fr []) = true /\
  fault_msg_did_pasid (frcd_of fr) = (rid, pasid).
Proof.
  intros Hc Hcp Hroot Hp Hpp Hdiff Hinv Hs1 Hze Hrec.
  (* the recorded fault is the stage-2 fault for (rid, pasid, va) *)
  assert (Hspec : vtd_record_fault contexts rid ptes pasid
                    (Machine_mem (iommu_shootdown_via_queue m root va p)) va
                  = Some {| FaultRecord_did := rid; FaultRecord_pasid := pasid;
                           FaultRecord_iova := va; FaultRecord_reason := FR_Stage2Fault |}).
  { apply (vtd_record_fault_stage2_spec contexts rid ptes pasid
             (Machine_mem (iommu_shootdown_via_queue m root va p)) va
             c e gpa perm1 Hc Hcp Hp Hpp Hs1).
    rewrite Hroot. rewrite Hze.
    rewrite (iommu_shootdown_via_queue_mem m root va p).
    apply (iommu_invalidate_faults root m.(Machine_mem) va p Hinv). }
  rewrite Hspec in Hrec.
  injection Hrec as Hfr. subst fr.
  split; cbn; reflexivity.
Qed.

(* Executable vector: after the shootdown of the freed frame the fault is
   recorded, the FRCD pending, and the message carries (0, 0). *)
Lemma test_vector_vtd_frcd_pending :
  vtd_record_fault [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry] 0
    (Machine_mem (iommu_shootdown_via_queue vtd_shoot_m vtd_s2_root va0 invalid_pte)) va0
  = Some {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := va0;
            FaultRecord_reason := FR_Stage2Fault |} /\
  frcd_pending (frcd_record {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := va0;
                              FaultRecord_reason := FR_Stage2Fault |} []) = true /\
  fault_msg_did_pasid (frcd_of {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := va0;
                                 FaultRecord_reason := FR_Stage2Fault |}) = (0, 0).
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================
   S4.5 PASID in-loop translation with fill-on-miss: the IOMMU's translation
   service loop consults the PASID cache; a hit walks the cached root, a miss
   re-walks the PASID table, refills the cache with the table's root, and
   walks.  After an eviction the *loop* recovers — it answers with the table
   result (unlike the raw evicted `pasid_cached_walk`, which misses) and
   leaves a refilled cache that is coherent again.
   ============================================================ *)

(* A cache hit walks the cached first-stage root and leaves the cache alone. *)
Lemma pasid_translate_fill_hit (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (ec : PasidCacheEntry) :
  pasid_cache_lookup cache pasid = Some ec ->
  ec.(PasidCacheEntry_present) = true ->
  pasid_translate_fill contexts rid ptes cache pasid mem iova
  = (pasid_cached_walk contexts rid cache pasid mem iova, cache).
Proof.
  intros Hcl Hcp.
  unfold pasid_translate_fill. rewrite Hcl. cbn. rewrite Hcp. cbn. reflexivity.
Qed.

(* A miss (non-present slot) with a present table entry re-walks the table and
   refills the cache with the table's first-stage root. *)
Lemma pasid_translate_fill_miss_refills (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (ec : PasidCacheEntry) (te : VtdPasid) :
  pasid_cache_lookup cache pasid = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = true ->
  pasid_translate_fill contexts rid ptes cache pasid mem iova
  = (vtd_walk_pasid contexts rid ptes pasid mem iova,
     pasid_cache_refill cache pasid te.(VtdPasid_s1_root)).
Proof.
  intros Hcl Hcp Hp Htp.
  unfold pasid_translate_fill. rewrite Hcl. cbn. rewrite Hcp. cbn. rewrite Hp. cbn. rewrite Htp. cbn. reflexivity.
Qed.

(* A miss with no table entry faults and leaves the cache alone (no refill on
   a fault). *)
Lemma pasid_translate_fill_miss_missing_table (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (ec : PasidCacheEntry) :
  pasid_cache_lookup cache pasid = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  vtd_pasid_lookup ptes pasid = None ->
  pasid_translate_fill contexts rid ptes cache pasid mem iova = (None, cache).
Proof.
  intros Hcl Hcp Hp.
  unfold pasid_translate_fill. rewrite Hcl. cbn. rewrite Hcp. cbn. rewrite Hp. cbn. reflexivity.
Qed.

(* A miss with a non-present table entry faults and leaves the cache alone. *)
Lemma pasid_translate_fill_miss_nonpresent_table (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (ec : PasidCacheEntry) (te : VtdPasid) :
  pasid_cache_lookup cache pasid = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = false ->
  pasid_translate_fill contexts rid ptes cache pasid mem iova = (None, cache).
Proof.
  intros Hcl Hcp Hp Htp.
  unfold pasid_translate_fill. rewrite Hcl. cbn. rewrite Hcp. cbn. rewrite Hp. cbn. rewrite Htp. cbn. reflexivity.
Qed.

(* After an eviction the in-loop translation recovers: it re-walks the table
   and refills, so it answers with the table result (not a miss) and leaves a
   refilled cache — the invalidation-then-retranslate cycle inside the loop. *)
Theorem pasid_translate_fill_after_evict (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (ec : PasidCacheEntry) (te : VtdPasid) :
  pasid_cache_lookup cache pasid = Some ec ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = true ->
  pasid_translate_fill contexts rid ptes (pasid_cache_evict cache pasid) pasid mem iova
  = (vtd_walk_pasid contexts rid ptes pasid mem iova,
     pasid_cache_refill (pasid_cache_evict cache pasid) pasid te.(VtdPasid_s1_root)).
Proof.
  intros Hcl Hp Htp.
  destruct (pasid_cache_evict_lookup cache pasid ec Hcl) as [ec' [Hev Hpev]].
  apply (pasid_translate_fill_miss_refills contexts rid ptes (pasid_cache_evict cache pasid)
            pasid mem iova ec' te Hev Hpev Hp Htp).
Qed.

(* Executable vector: evicting PASID 0 then translating through the loop
   answers with the table hit and refills the cache. *)
Lemma test_vector_pasid_translate_fill_after_evict :
  pasid_translate_fill [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry]
    (pasid_cache_evict [vtd_coherent_cache_entry] 0) 0 mem_vtd_pasid_hit va0
  = (Some (expected_pa, Read),
     pasid_cache_refill (pasid_cache_evict [vtd_coherent_cache_entry] 0) 0 vtd_s1_root).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.5 FRCD interrupt delivery into the core interrupt controller: a pending
   FRCD raises the fault line on the target core through the INTC's send
   (edge-triggered, latched regardless of mask/delivery, IHI0069 4.4), and the
   kernel's unmasked, delivery-enabled ack rings the doorbell — the S4.5 tie
   into SSG-3's intc model.
   ============================================================ *)

(* The IOMMU's fault signal: raise the INTC line for the target core iff the
   FRCD holds a fault; a drained FRCD signals nothing. *)
Definition frcd_signal_intc (frcd : list FrcdEntry) (ic : intc_types.Intc) (core : Z) : intc_types.Intc :=
  if frcd_pending frcd then intc.intc_send ic core else ic.

(* A pending FRCD raises the fault line on the target core — latched even if
   the core is masked or in interrupt context. *)
Lemma frcd_signal_raises (frcd : list FrcdEntry) (ic : intc_types.Intc) (core : nat)
    (Hlen : Nat.lt core (length (intc_types.Intc_pending ic))) :
  frcd_pending frcd = true ->
  intc.intc_get_bit (intc_types.Intc_pending (frcd_signal_intc frcd ic (Z.of_nat core)))
    (Z.of_nat core) false = true.
Proof.
  intros Hfr. unfold frcd_signal_intc. rewrite Hfr.
  apply (intc_send_sets_pending ic core Hlen).
Qed.

(* A drained FRCD signals nothing: the controller is untouched. *)
Lemma frcd_signal_drained_noop (frcd : list FrcdEntry) (ic : intc_types.Intc) (core : Z) :
  frcd_pending frcd = false -> frcd_signal_intc frcd ic core = ic.
Proof. intros Hfr. unfold frcd_signal_intc. rewrite Hfr. reflexivity. Qed.

(* The full chain: after the queue shootdown of the freed frame, the fault is
   recorded, the FRCD is pending, and the IOMMU raises the fault line on the
   target core. *)
Theorem vtd_shootdown_frcd_delivers (m : Machine) (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (pasid : Z) (c : VtdContext) (e : VtdPasid)
    (root : mword 44) (va : mword 64) (p : Pte) (gpa : mword 56) (perm1 : Perm)
    (fr : FaultRecord) (ic : intc_types.Intc) (core : nat) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  c.(VtdContext_sl_root) = root ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  e.(VtdPasid_s1_root) <> root ->
  p.(Pte_valid) = false ->
  iommu_walk e.(VtdPasid_s1_root) (Machine_mem (iommu_shootdown_via_queue m root va p)) va = Some (gpa, perm1) ->
  zero_extend gpa 64 = va ->
  vtd_record_fault contexts rid ptes pasid (Machine_mem (iommu_shootdown_via_queue m root va p)) va = Some fr ->
  Nat.lt core (length (intc_types.Intc_pending ic)) ->
  intc.intc_get_bit (intc_types.Intc_pending
                       (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core)))
    (Z.of_nat core) false = true.
Proof.
  intros Hc Hcp Hroot Hp Hpp Hdiff Hinv Hs1 Hze Hrec Hlen.
  apply (frcd_signal_raises (frcd_record fr []) ic core Hlen).
  apply (proj1 (vtd_shootdown_frcd_pending m contexts rid ptes pasid c e root va p gpa perm1 fr
                  Hc Hcp Hroot Hp Hpp Hdiff Hinv Hs1 Hze Hrec)).
Qed.

(* The kernel's unmasked, delivery-enabled ack of the fault rings the
   doorbell — the delivered bit that Machine.ipi consumes. *)
Lemma vtd_fault_ack_rings (frcd : list FrcdEntry) (ic : intc_types.Intc) (core : nat)
    (Hfr : frcd_pending frcd = true)
    (Hm : intc.intc_get_bit (intc_types.Intc_masked ic) (Z.of_nat core) false = false)
    (Hd : intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat core) false = true)
    (Hlen : Nat.lt core (length (intc_types.Intc_pending ic))) :
  intc_types.Intc_ipi (intc.intc_ack (frcd_signal_intc frcd ic (Z.of_nat core)) (Z.of_nat core))
  = intc.intc_set_bit (intc_types.Intc_ipi ic) (Z.of_nat core) true.
Proof.
  unfold frcd_signal_intc. rewrite Hfr.
  assert (Hsend : intc.intc_get_bit (intc_types.Intc_pending (intc.intc_send ic (Z.of_nat core)))
                    (Z.of_nat core) false = true)
    by (apply (intc_send_sets_pending ic core Hlen)).
  assert (Hm' : intc.intc_get_bit (intc_types.Intc_masked (intc.intc_send ic (Z.of_nat core)))
                  (Z.of_nat core) false = false).
  { rewrite (intc_send_preserves_masked ic (Z.of_nat core)). exact Hm. }
  assert (Hd' : intc.intc_get_bit (intc_types.Intc_delivery (intc.intc_send ic (Z.of_nat core)))
                  (Z.of_nat core) false = true).
  { rewrite (intc_send_preserves_delivery ic (Z.of_nat core)). exact Hd. }
  rewrite (intc_ack_unmasked_rings (intc.intc_send ic (Z.of_nat core)) core Hsend Hm' Hd').
  rewrite (intc_send_preserves_ipi ic (Z.of_nat core)). reflexivity.
Qed.

(* Executable vectors: a recorded stage-2 fault raises the INTC line for core
   0, and the kernel's ack (unmasked, delivery enabled) rings the doorbell. *)
Definition vtd_intc0 : intc_types.Intc :=
  {| intc_types.Intc_pending := [false]; intc_types.Intc_masked := [false];
     intc_types.Intc_delivery := [true]; intc_types.Intc_ipi := [false] |}.

Lemma test_vector_vtd_frcd_delivers :
  intc.intc_get_bit (intc_types.Intc_pending
                       (frcd_signal_intc (frcd_record {| FaultRecord_did := 0; FaultRecord_pasid := 0;
                                                         FaultRecord_iova := va0;
                                                         FaultRecord_reason := FR_Stage2Fault |} [])
                                         vtd_intc0 0))
    0 false = true.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_vtd_frcd_ack_rings :
  intc_types.Intc_ipi
    (intc.intc_ack (frcd_signal_intc (frcd_record {| FaultRecord_did := 0; FaultRecord_pasid := 0;
                                                     FaultRecord_iova := va0;
                                                     FaultRecord_reason := FR_Stage2Fault |} [])
                                      vtd_intc0 0) 0)
  = [true].
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.5 DTE PASID-table pointers: the scalable-mode two-stage walk goes
   DTE -> PASID table -> first stage, then the selected context's second
   level; it agrees with the flat `vtd_walk_pasid` exactly when the DTE's
   PASID-table pointer selects the shared table and its ctx_index selects the
   context the flat lookup would find.
   ============================================================ *)

(* The scalable-mode walk reduces to the two-stage composition given the
   DTE, PASID-table, PASID-entry, and context resolutions. *)
Lemma vtd_walk_device_pasid_two_stage (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) (ptes : list VtdPasid) (e : VtdPasid) (c : VtdContext) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = Some ptes ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  vtd_context_lookup contexts d.(VtdDeviceEntry_ctx_index) = Some c ->
  c.(VtdContext_present) = true ->
  vtd_walk_device_pasid devtbl tbls contexts rid pasid mem iova
  = match iommu_walk e.(VtdPasid_s1_root) mem iova with
    | None => None
    | Some (gpa, _) => iommu_walk c.(VtdContext_sl_root) mem (zero_extend gpa 64)
    end.
Proof.
  intros Hd Hdp Ht Hp Hpp Hc Hcp.
  unfold vtd_walk_device_pasid. rewrite Hd, Hdp, Ht, Hp, Hpp, Hc, Hcp. cbn. reflexivity.
Qed.

(* The DTE's PASID table + context selection aliasing the flat view: when the
   DTE's PASID-table pointer selects the shared table and its ctx_index the
   context the flat lookup would find, the scalable-mode walk equals
   `vtd_walk_pasid`. *)
Lemma vtd_walk_device_pasid_of_flat (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) (ptes : list VtdPasid) (e : VtdPasid) (c : VtdContext) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  d.(VtdDeviceEntry_ctx_index) = rid ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = Some ptes ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_walk_device_pasid devtbl tbls contexts rid pasid mem iova
  = vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hd Hdp Hidx Ht Hp Hpp Hc Hcp.
  assert (Hc' : vtd_context_lookup contexts (VtdDeviceEntry_ctx_index d) = Some c)
    by (rewrite Hidx; exact Hc).
  rewrite (vtd_walk_device_pasid_two_stage devtbl tbls contexts rid pasid mem iova
            d ptes e c Hd Hdp Ht Hp Hpp Hc' Hcp).
  rewrite (vtd_walk_pasid_two_stage contexts rid ptes pasid mem iova c e Hc Hcp Hp Hpp).
  reflexivity.
Qed.

(* Faults: missing DTE, non-present DTE, missing PASID table, missing PASID
   entry, and non-present PASID entry each fault the scalable-mode walk. *)
Lemma vtd_walk_device_pasid_missing_fault (tbls : list (list VtdPasid)) (contexts : list VtdContext)
    (rid pasid : Z) (mem : list MemEntry) (iova : mword 64) :
  vtd_walk_device_pasid [] tbls contexts rid pasid mem iova = None.
Proof. unfold vtd_walk_device_pasid. cbn. reflexivity. Qed.

Lemma vtd_walk_device_pasid_nonpresent_fault (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = false ->
  vtd_walk_device_pasid devtbl tbls contexts rid pasid mem iova = None.
Proof. intros Hd Hdp. unfold vtd_walk_device_pasid. rewrite Hd, Hdp. cbn. reflexivity. Qed.

Lemma vtd_walk_device_pasid_missing_table_fault (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = None ->
  vtd_walk_device_pasid devtbl tbls contexts rid pasid mem iova = None.
Proof. intros Hd Hdp Ht. unfold vtd_walk_device_pasid. rewrite Hd, Hdp, Ht. cbn. reflexivity. Qed.

Lemma vtd_walk_device_pasid_missing_entry_fault (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) (ptes : list VtdPasid) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = Some ptes ->
  vtd_pasid_lookup ptes pasid = None ->
  vtd_walk_device_pasid devtbl tbls contexts rid pasid mem iova = None.
Proof.
  intros Hd Hdp Ht Hp. unfold vtd_walk_device_pasid. rewrite Hd, Hdp, Ht, Hp. cbn. reflexivity.
Qed.

Lemma vtd_walk_device_pasid_nonpresent_entry_fault (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) (ptes : list VtdPasid) (e : VtdPasid) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = Some ptes ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = false ->
  vtd_walk_device_pasid devtbl tbls contexts rid pasid mem iova = None.
Proof.
  intros Hd Hdp Ht Hp Hpp. unfold vtd_walk_device_pasid. rewrite Hd, Hdp, Ht, Hp, Hpp. cbn. reflexivity.
Qed.

(* Executable vector: a present DTE for rid 0 whose PASID-table pointer
   selects the hit table resolves the two-stage walk to the same SPA as the
   flat walk. *)
Definition vtd_dev_pasid_hit_entry : VtdDeviceEntry :=
  {| VtdDeviceEntry_present := true; VtdDeviceEntry_did := 7; VtdDeviceEntry_ctx_index := 0;
     VtdDeviceEntry_pasid_tbl := 0 |}.

Lemma test_vector_vtd_walk_device_pasid_hit :
  vtd_walk_device_pasid [vtd_dev_pasid_hit_entry] [ [vtd_pasid_hit_entry] ] [vtd_pasid_hit_context]
    0 0 mem_vtd_pasid_hit va0 = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

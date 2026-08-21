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
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
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
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
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
  match (vtd_context_lookup contexts rid, vtd_pasid_lookup ptes pasid, pasid_cache_lookup cache (rid, pasid)) with
  | (Some c, Some e, Some ec) =>
      c.(VtdContext_present) = true -> e.(VtdPasid_present) = true ->
      ec.(PasidCacheEntry_present) = true /\
      ec.(PasidCacheEntry_did) = rid /\
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
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  pasid_cached_walk contexts rid cache pasid mem iova =
  vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hcoh Hc Hcp Hp Hpp Hcl.
  unfold pasid_cache_coherent in Hcoh.
  rewrite Hc, Hp, Hcl in Hcoh. cbn in Hcoh.
  specialize (Hcoh Hcp). specialize (Hcoh Hpp).
  destruct Hcoh as [Hcpp [Hdid [Hpasid Hs1root]]].
  apply (pasid_cached_walk_of_table contexts rid ptes cache pasid mem iova c e ec
            Hc Hcp Hp Hpp Hcl Hcpp Hs1root).
Qed.

(* Executable vector: a coherent cache entry makes the cached walk resolve to
   the same SPA as the table-driven two-stage walk. *)
Definition vtd_coherent_cache_entry : PasidCacheEntry :=
  {| PasidCacheEntry_present := true; PasidCacheEntry_did := 0; PasidCacheEntry_pasid := 0; PasidCacheEntry_gen := 0;
     PasidCacheEntry_s1_root := vtd_s1_root |}.

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
   S4.5 PASID-cache tags (DID+PASID) + eviction / refill: the cache is tagged
   by (DID, PASID), so the lookup scans by tag equality (not by position),
   eviction clears every entry of a DID (device-selective invalidation, VT-d
   5.20 §6.5.2.4), and refill re-installs the table's root under the full tag.
   Eviction breaks `pasid_cache_coherent`; refill restores it — the
   miss/refill cycle a translation after invalidation must go through.
   ============================================================ *)

(* A found entry always carries the tag it was looked up by. *)
Lemma pasid_cache_lookup_tagged (cache : list PasidCacheEntry) (did pasid : Z) (ec : PasidCacheEntry) :
  pasid_cache_lookup cache (did, pasid) = Some ec ->
  ec.(PasidCacheEntry_did) = did /\ ec.(PasidCacheEntry_pasid) = pasid.
Proof.
  revert did pasid. induction cache as [| e rest IH]; cbn; intros did pasid H.
  - discriminate.
  - destruct (Z.eqb_spec e.(PasidCacheEntry_did) did) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec e.(PasidCacheEntry_pasid) pasid) as [Hp | Hp]; cbn in H.
      * injection H as ->. auto.
      * exact (IH did pasid H).
    + exact (IH did pasid H).
Qed.

(* Eviction by DID clears the device's entry: the (did, pasid) lookup afterwards
   returns the same entry, non-present — the cache-miss state. *)
Lemma pasid_cache_evict_lookup (cache : list PasidCacheEntry) (did pasid : Z) (ec : PasidCacheEntry) :
  pasid_cache_lookup cache (did, pasid) = Some ec ->
  exists ec', pasid_cache_lookup (pasid_cache_evict cache did) (did, pasid) = Some ec' /\
             ec'.(PasidCacheEntry_present) = false.
Proof.
  revert did pasid. induction cache as [| e rest IH]; cbn; intros did pasid H.
  - discriminate.
  - destruct (Z.eqb_spec e.(PasidCacheEntry_did) did) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec e.(PasidCacheEntry_pasid) pasid) as [Hp | Hp]; cbn in H.
      * injection H as <-.
        exists {| PasidCacheEntry_present := false; PasidCacheEntry_did := e.(PasidCacheEntry_did);
                 PasidCacheEntry_pasid := e.(PasidCacheEntry_pasid); PasidCacheEntry_gen := e.(PasidCacheEntry_gen);
                 PasidCacheEntry_s1_root := e.(PasidCacheEntry_s1_root) |}.
        cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp). cbn. split; reflexivity.
      * cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH did pasid H).
    + cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH did pasid H).
Qed.

(* The evicted device's cached walk misses: the slot is non-present, so the
   cached two-stage walk faults — the IOMMU must re-walk the PASID table. *)
Lemma pasid_cached_walk_evict_misses (contexts : list VtdContext) (rid : Z)
    (cache : list PasidCacheEntry) (pasid : Z) (mem : list MemEntry) (iova : mword 64)
    (c : VtdContext) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  pasid_cached_walk contexts rid (pasid_cache_evict cache rid) pasid mem iova = None.
Proof.
  intros Hc Hcp Hcl.
  destruct (pasid_cache_evict_lookup cache rid pasid ec Hcl) as [ec' [Hcl' Hp']].
  unfold pasid_cached_walk. rewrite Hc, Hcp, Hcl'. cbn. rewrite Hp'. cbn. reflexivity.
Qed.

(* Eviction is selective per device: entries under any other DID are untouched. *)
Lemma pasid_cache_evict_preserves_other_did (cache : list PasidCacheEntry) (did did' pasid' : Z) :
  did <> did' ->
  forall e, pasid_cache_lookup cache (did', pasid') = Some e ->
         pasid_cache_lookup (pasid_cache_evict cache did) (did', pasid') = Some e.
Proof.
  revert did did' pasid'. induction cache as [| h rest IH]; cbn; intros did did' pasid' Hneq e H.
  - discriminate.
  - destruct (Z.eqb_spec h.(PasidCacheEntry_did) did) as [Hd | Hd]; cbn in H.
    + (* h.did = did <> did' — eviction turns h non-present; the target tag
         (did', pasid') cannot match the head, so the lookup skips it. *)
      assert (Hhead : Z.eqb h.(PasidCacheEntry_did) did' = false).
      { apply Z.eqb_neq. intros Hsub. apply Hneq. congruence. }
      rewrite Hhead in H. cbn in H.
      cbn. rewrite Hhead. cbn. exact (IH did did' pasid' Hneq e H).
    + (* h.did <> did — eviction keeps the head untouched. *)
      destruct (Z.eqb_spec h.(PasidCacheEntry_did) did') as [Hd' | Hd']; cbn in H.
      * destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) pasid') as [Hp' | Hp']; cbn in H.
        -- cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd'), (proj2 (Z.eqb_eq _ _) Hp'). cbn. exact H.
        -- cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd'), (proj2 (Z.eqb_neq _ _) Hp'). cbn. exact (IH did did' pasid' Hneq e H).
      * cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd'). cbn. exact (IH did did' pasid' Hneq e H).
Qed.

(* Refill re-installs the evicted slot as present with the given root. *)
Lemma pasid_cache_refill_lookup (cache : list PasidCacheEntry) (did pasid : Z) (root : mword 44)
    (ec : PasidCacheEntry) :
  pasid_cache_lookup cache (did, pasid) = Some ec ->
  exists ec', pasid_cache_lookup (pasid_cache_refill cache (did, pasid) root) (did, pasid) = Some ec' /\
             ec'.(PasidCacheEntry_present) = true /\
             ec'.(PasidCacheEntry_s1_root) = root.
Proof.
  revert did pasid. induction cache as [| e rest IH]; cbn; intros did pasid H.
  - discriminate.
  - destruct (Z.eqb_spec e.(PasidCacheEntry_did) did) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec e.(PasidCacheEntry_pasid) pasid) as [Hp | Hp]; cbn in H.
      * injection H as <-.
        exists {| PasidCacheEntry_present := true; PasidCacheEntry_did := e.(PasidCacheEntry_did);
                 PasidCacheEntry_pasid := e.(PasidCacheEntry_pasid); PasidCacheEntry_gen := e.(PasidCacheEntry_gen);
                 PasidCacheEntry_s1_root := root |}.
        cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp). cbn. repeat split; reflexivity.
      * cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH did pasid H).
    + cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH did pasid H).
Qed.

(* Refill on a never-present tag installs a fresh entry carrying the full tag
   — the hardware fill-on-miss path (no evicted slot to re-validate). *)
Lemma pasid_cache_refill_fresh (cache : list PasidCacheEntry) (did pasid : Z) (root : mword 44) :
  pasid_cache_lookup cache (did, pasid) = None ->
  pasid_cache_lookup (pasid_cache_refill cache (did, pasid) root) (did, pasid)
  = Some {| PasidCacheEntry_present := true; PasidCacheEntry_did := did;
           PasidCacheEntry_pasid := pasid; PasidCacheEntry_gen := 0; PasidCacheEntry_s1_root := root |}.
Proof.
  revert did pasid. induction cache as [| e rest IH]; cbn; intros did pasid H.
  - rewrite (proj2 (Z.eqb_eq did did) eq_refl), (proj2 (Z.eqb_eq pasid pasid) eq_refl). cbn. reflexivity.
  - destruct (Z.eqb_spec e.(PasidCacheEntry_did) did) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec e.(PasidCacheEntry_pasid) pasid) as [Hp | Hp]; cbn in H.
      * discriminate.
      * cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH did pasid H).
    + cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH did pasid H).
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
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  pasid_cached_walk contexts rid (pasid_cache_refill cache (rid, pasid) e.(VtdPasid_s1_root)) pasid mem iova
  = vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hc Hcp Hp Hpp Hcl.
  destruct (pasid_cache_refill_lookup cache rid pasid e.(VtdPasid_s1_root) ec Hcl) as [ec' [Hcl' [Hp' Hs]]].
  apply (pasid_cached_walk_of_table contexts rid ptes (pasid_cache_refill cache (rid, pasid) e.(VtdPasid_s1_root))
           pasid mem iova c e ec' Hc Hcp Hp Hpp Hcl' Hp' Hs).
Qed.

(* The evict → refill cycle: eviction breaks the cached walk for the device's
   PASID (a miss), and refilling with the table's root restores the
   table-driven result — the invalidation-then-retranslate cycle. *)
Theorem pasid_cache_evict_refill_cycle (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) (e : VtdPasid) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  pasid_cached_walk contexts rid (pasid_cache_evict cache rid) pasid mem iova = None /\
  pasid_cached_walk contexts rid (pasid_cache_refill (pasid_cache_evict cache rid) (rid, pasid)
                                    e.(VtdPasid_s1_root)) pasid mem iova
  = vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hc Hcp Hp Hpp Hcl.
  destruct (pasid_cache_evict_lookup cache rid pasid ec Hcl) as [ec' [Hev Hpev]].
  split.
  - apply (pasid_cached_walk_evict_misses contexts rid cache pasid mem iova c ec Hc Hcp Hcl).
  - apply (pasid_cache_refill_coherent contexts rid ptes (pasid_cache_evict cache rid) pasid
             mem iova c e ec' Hc Hcp Hp Hpp Hev).
Qed.

(* Executable vector: evicting DID 0 turns the cached walk into a miss. *)
Lemma test_vector_vtd_pasid_cache_evict :
  pasid_cached_walk [vtd_pasid_hit_context] 0
    (pasid_cache_evict [vtd_coherent_cache_entry] 0) 0 mem_vtd_pasid_hit va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* Executable vector: the tag is (DID, PASID) — evicting DID 0 leaves the
   other device's (1, 0) entry present and findable, while the (0, 0) entry
   is cleared (non-present, still tagged). *)
Definition vtd_coherent_cache_entry_did1 : PasidCacheEntry :=
  {| PasidCacheEntry_present := true; PasidCacheEntry_did := 1; PasidCacheEntry_pasid := 0; PasidCacheEntry_gen := 0;
     PasidCacheEntry_s1_root := vtd_s1_root |}.

Lemma test_vector_vtd_pasid_cache_tags :
  pasid_cache_lookup [vtd_coherent_cache_entry; vtd_coherent_cache_entry_did1] (0, 0)
  = Some vtd_coherent_cache_entry /\
  pasid_cache_lookup (pasid_cache_evict [vtd_coherent_cache_entry; vtd_coherent_cache_entry_did1] 0) (1, 0)
  = Some vtd_coherent_cache_entry_did1 /\
  pasid_cache_lookup (pasid_cache_evict [vtd_coherent_cache_entry; vtd_coherent_cache_entry_did1] 0) (0, 0)
  = Some {| PasidCacheEntry_present := false; PasidCacheEntry_did := 0; PasidCacheEntry_pasid := 0; PasidCacheEntry_gen := 0;
           PasidCacheEntry_s1_root := vtd_s1_root |}.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================
   S4.5 PASID-cache invalidation granularity (VT-d 5.20 §6.5.2.4): the
   PASID-cache Invalidation Descriptor's granularity selects a single
   (DID, PASID) tag, an entire DID (domain-selective), or the whole cache
   (global).  Each clears exactly its scope: the tagged entry is turned
   non-present, entries under other tags survive.
   ============================================================ *)

(* PASID-selective: clearing the (did, pasid) tag makes the tagged lookup
   miss — the cache-miss state for that one PASID (granularity 01b). *)
Lemma pasid_cache_evict_pasid_clears (cache : list PasidCacheEntry) (did pasid : Z) (ec : PasidCacheEntry) :
  pasid_cache_lookup cache (did, pasid) = Some ec ->
  exists ec', pasid_cache_lookup (pasid_cache_evict_pasid cache (did, pasid)) (did, pasid) = Some ec' /\
             ec'.(PasidCacheEntry_present) = false.
Proof.
  revert did pasid. induction cache as [| e rest IH]; cbn; intros did pasid H.
  - discriminate.
  - destruct (Z.eqb_spec e.(PasidCacheEntry_did) did) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec e.(PasidCacheEntry_pasid) pasid) as [Hp | Hp]; cbn in H.
      * injection H as <-.
        exists {| PasidCacheEntry_present := false; PasidCacheEntry_did := e.(PasidCacheEntry_did);
                 PasidCacheEntry_pasid := e.(PasidCacheEntry_pasid); PasidCacheEntry_gen := e.(PasidCacheEntry_gen);
                 PasidCacheEntry_s1_root := e.(PasidCacheEntry_s1_root) |}.
        cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp). cbn. split; reflexivity.
      * cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH did pasid H).
    + cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH did pasid H).
Qed.

(* Global: clearing every entry makes the (did, pasid) lookup miss too
   (granularity 11b). *)
Lemma pasid_cache_evict_all_clears (cache : list PasidCacheEntry) (did pasid : Z) (ec : PasidCacheEntry) :
  pasid_cache_lookup cache (did, pasid) = Some ec ->
  exists ec', pasid_cache_lookup (pasid_cache_evict_all cache) (did, pasid) = Some ec' /\
             ec'.(PasidCacheEntry_present) = false.
Proof.
  revert did pasid. induction cache as [| e rest IH]; cbn; intros did pasid H.
  - discriminate.
  - destruct (Z.eqb_spec e.(PasidCacheEntry_did) did) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec e.(PasidCacheEntry_pasid) pasid) as [Hp | Hp]; cbn in H.
      * injection H as <-.
        exists {| PasidCacheEntry_present := false; PasidCacheEntry_did := e.(PasidCacheEntry_did);
                 PasidCacheEntry_pasid := e.(PasidCacheEntry_pasid); PasidCacheEntry_gen := e.(PasidCacheEntry_gen);
                 PasidCacheEntry_s1_root := e.(PasidCacheEntry_s1_root) |}.
        (* Global eviction has no guard — the destructs already made the
           lookup's tag guards concrete, so cbn reduces straight to the
           evicted entry. *)
        cbn. split; reflexivity.
      * cbn. exact (IH did pasid H).
    + cbn. exact (IH did pasid H).
Qed.

(* PASID-selective invalidation is selective per tag: entries under a
   *different* (did, pasid) tag are untouched. *)
Lemma pasid_cache_evict_pasid_preserves_other (cache : list PasidCacheEntry)
    (did pasid did' pasid' : Z) :
  did <> did' \/ pasid <> pasid' ->
  forall e, pasid_cache_lookup cache (did', pasid') = Some e ->
         pasid_cache_lookup (pasid_cache_evict_pasid cache (did, pasid)) (did', pasid') = Some e.
Proof.
  revert did pasid did' pasid'. induction cache as [| h rest IH]; cbn; intros did pasid did' pasid' Hneq e H.
  - discriminate.
  - destruct (Z.eqb_spec h.(PasidCacheEntry_did) did) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) pasid) as [Hp | Hp]; cbn in H.
      (* h carries the evicted tag (did, pasid) — it is turned non-present.
         The target tag (did', pasid') differs in at least one component, so
         the lookup's head guard is false and it recurses. *)
      * destruct Hneq as [Hd' | Hp'].
        -- assert (Hd'f : Z.eqb h.(PasidCacheEntry_did) did' = false).
           { apply Z.eqb_neq. intros Hsub. apply Hd'. congruence. }
           rewrite Hd'f in H. cbn in H. cbn. rewrite Hd'f. cbn.
           exact (IH did pasid did' pasid' (or_introl Hd') e H).
        -- assert (Hp'f : Z.eqb h.(PasidCacheEntry_pasid) pasid' = false).
           { apply Z.eqb_neq. intros Hsub. apply Hp'. congruence. }
           rewrite Hp'f in H. rewrite Bool.andb_false_r in H. cbn in H.
           cbn. rewrite Hp'f. rewrite Bool.andb_false_r. cbn.
           exact (IH did pasid did' pasid' (or_intror Hp') e H).
      * (* h.did = did but h.pasid <> pasid — the evict keeps the head
           untouched, so both sides reduce by the same (did', pasid') tag
           guard on the head. *)
        cbn. destruct (Z.eqb h.(PasidCacheEntry_did) did') eqn:Hd'';
              destruct (Z.eqb h.(PasidCacheEntry_pasid) pasid') eqn:Hp''; cbn;
              (* The destructs substitute the head's tag guard in both the goal
                 and H — cbn reduces both sides to the kept head or the tail. *)
              cbn in H;
              first [ exact H | exact (IH did pasid did' pasid' Hneq e H) ].
    + (* h.did <> did — the evict keeps the head untouched. *)
      destruct (Z.eqb_spec h.(PasidCacheEntry_did) did') as [Hd' | Hd']; cbn in H.
      * destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) pasid') as [Hp' | Hp']; cbn in H.
        (* The destructs substitute the guard in H (so cbn in H reduces it),
           while the goal keeps the head's tag guard symbolic — rewrite the
           eqns in to decide it. *)
        -- cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd'), (proj2 (Z.eqb_eq _ _) Hp'). cbn. exact H.
        -- cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd'), (proj2 (Z.eqb_neq _ _) Hp'). cbn.
           exact (IH did pasid did' pasid' Hneq e H).
      * cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd'). cbn. exact (IH did pasid did' pasid' Hneq e H).
Qed.

(* The evict → refill cycle at PASID granularity: evicting the (did, pasid)
   tag breaks the cached walk, and refilling with the table root restores the
   table-driven result — the invalidation-then-retranslate cycle. *)
Theorem pasid_cache_evict_pasid_refill_cycle (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) (e : VtdPasid) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  pasid_cached_walk contexts rid (pasid_cache_evict_pasid cache (rid, pasid)) pasid mem iova = None /\
  pasid_cached_walk contexts rid (pasid_cache_refill (pasid_cache_evict_pasid cache (rid, pasid)) (rid, pasid)
                                    e.(VtdPasid_s1_root)) pasid mem iova
  = vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hc Hcp Hp Hpp Hcl.
  destruct (pasid_cache_evict_pasid_clears cache rid pasid ec Hcl) as [ec' [Hev Hpev]].
  split.
  - unfold pasid_cached_walk. rewrite Hc, Hcp, Hev. cbn. rewrite Hpev. cbn. reflexivity.
  - apply (pasid_cache_refill_coherent contexts rid ptes (pasid_cache_evict_pasid cache (rid, pasid)) pasid
             mem iova c e ec' Hc Hcp Hp Hpp Hev).
Qed.

(* Executable vectors: PASID-selective invalidation clears only the (0, 0)
   tag — the same DID's other PASID (0, 1) survives; global invalidation
   clears everything (entries stay tagged, present cleared). *)
Definition vtd_coherent_cache_entry_pasid1 : PasidCacheEntry :=
  {| PasidCacheEntry_present := true; PasidCacheEntry_did := 0; PasidCacheEntry_pasid := 1; PasidCacheEntry_gen := 0;
     PasidCacheEntry_s1_root := vtd_s1_root |}.

Lemma test_vector_vtd_pasid_cache_granularity :
  pasid_cache_lookup (pasid_cache_evict_pasid [vtd_coherent_cache_entry; vtd_coherent_cache_entry_pasid1] (0, 0)) (0, 1)
  = Some vtd_coherent_cache_entry_pasid1 /\
  pasid_cache_lookup (pasid_cache_evict_pasid [vtd_coherent_cache_entry; vtd_coherent_cache_entry_pasid1] (0, 0)) (0, 0)
  = Some {| PasidCacheEntry_present := false; PasidCacheEntry_did := 0; PasidCacheEntry_pasid := 0; PasidCacheEntry_gen := 0;
           PasidCacheEntry_s1_root := vtd_s1_root |} /\
  pasid_cache_lookup (pasid_cache_evict_all [vtd_coherent_cache_entry; vtd_coherent_cache_entry_pasid1]) (0, 1)
  = Some {| PasidCacheEntry_present := false; PasidCacheEntry_did := 0; PasidCacheEntry_pasid := 1; PasidCacheEntry_gen := 0;
           PasidCacheEntry_s1_root := vtd_s1_root |}.
Proof. vm_compute. repeat split; reflexivity. Qed.

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
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  ec.(PasidCacheEntry_present) = true ->
  pasid_translate_fill contexts rid ptes cache pasid mem iova
  = (pasid_cached_walk contexts rid cache pasid mem iova, cache).
Proof.
  intros Hcl Hcp.
  unfold pasid_translate_fill. rewrite Hcl. cbn. rewrite Hcp. cbn. reflexivity.
Qed.

(* A miss (non-present slot) with a present table entry re-walks the table and
   refills the cache with the table's first-stage root, under the full tag. *)
Lemma pasid_translate_fill_miss_refills (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (ec : PasidCacheEntry) (te : VtdPasid) :
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = true ->
  pasid_translate_fill contexts rid ptes cache pasid mem iova
  = (vtd_walk_pasid contexts rid ptes pasid mem iova,
     pasid_cache_refill cache (rid, pasid) te.(VtdPasid_s1_root)).
Proof.
  intros Hcl Hcp Hp Htp.
  unfold pasid_translate_fill. rewrite Hcl. cbn. rewrite Hcp. cbn. rewrite Hp. cbn. rewrite Htp. cbn. reflexivity.
Qed.

(* A miss with no table entry faults and leaves the cache alone (no refill on
   a fault). *)
Lemma pasid_translate_fill_miss_missing_table (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (ec : PasidCacheEntry) :
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
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
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
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
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = true ->
  pasid_translate_fill contexts rid ptes (pasid_cache_evict cache rid) pasid mem iova
  = (vtd_walk_pasid contexts rid ptes pasid mem iova,
     pasid_cache_refill (pasid_cache_evict cache rid) (rid, pasid) te.(VtdPasid_s1_root)).
Proof.
  intros Hcl Hp Htp.
  destruct (pasid_cache_evict_lookup cache rid pasid ec Hcl) as [ec' [Hev Hpev]].
  apply (pasid_translate_fill_miss_refills contexts rid ptes (pasid_cache_evict cache rid)
            pasid mem iova ec' te Hev Hpev Hp Htp).
Qed.

(* The in-loop refill carries the full (DID, PASID) tag: after a miss-refill
   the (rid, pasid) lookup returns a present entry holding the table's root. *)
Lemma pasid_translate_fill_refill_tagged (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (ec : PasidCacheEntry) (te : VtdPasid) :
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = true ->
  exists ec',
    pasid_cache_lookup (snd (pasid_translate_fill contexts rid ptes cache pasid mem iova)) (rid, pasid)
    = Some ec' /\
    ec'.(PasidCacheEntry_present) = true /\
    ec'.(PasidCacheEntry_did) = rid /\
    ec'.(PasidCacheEntry_pasid) = pasid /\
    ec'.(PasidCacheEntry_s1_root) = te.(VtdPasid_s1_root).
Proof.
  intros Hcl Hcp Hp Htp.
  rewrite (pasid_translate_fill_miss_refills contexts rid ptes cache pasid mem iova ec te Hcl Hcp Hp Htp).
  cbn.
  destruct (pasid_cache_refill_lookup cache rid pasid te.(VtdPasid_s1_root) ec Hcl) as [ec' [Hcl' [Hp' Hs]]].
  exists ec'. split; [exact Hcl' |].
  destruct (pasid_cache_lookup_tagged (pasid_cache_refill cache (rid, pasid) te.(VtdPasid_s1_root))
             rid pasid ec' Hcl') as [Hd' Hp''].
  repeat split; assumption.
Qed.

(* After an eviction the loop recovers to a *coherent* cache: the refilled
   entry matches the table, so the cache ⊆ table invariant holds again, and
   the loop's answer is the table-driven two-stage walk. *)
Theorem pasid_translate_fill_after_evict_refilled_coherent (contexts : list VtdContext) (rid : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry) (pasid : Z)
    (mem : list MemEntry) (iova : mword 64) (c : VtdContext) (e : VtdPasid) (ec : PasidCacheEntry) :
  vtd_context_lookup contexts rid = Some c ->
  c.(VtdContext_present) = true ->
  vtd_pasid_lookup ptes pasid = Some e ->
  e.(VtdPasid_present) = true ->
  pasid_cache_lookup cache (rid, pasid) = Some ec ->
  pasid_cache_coherent contexts rid ptes
    (snd (pasid_translate_fill contexts rid ptes (pasid_cache_evict cache rid) pasid mem iova)) pasid /\
  fst (pasid_translate_fill contexts rid ptes (pasid_cache_evict cache rid) pasid mem iova)
  = vtd_walk_pasid contexts rid ptes pasid mem iova.
Proof.
  intros Hc Hcp Hp Hpp Hcl.
  rewrite (pasid_translate_fill_after_evict contexts rid ptes cache pasid mem iova ec e Hcl Hp Hpp).
  cbn.
  destruct (pasid_cache_evict_lookup cache rid pasid ec Hcl) as [ec' [Hev Hpev]].
  split.
  - unfold pasid_cache_coherent. rewrite Hc, Hp. cbn.
    destruct (pasid_cache_refill_lookup (pasid_cache_evict cache rid) rid pasid e.(VtdPasid_s1_root) ec' Hev)
      as [ec'' [Hcl'' [Hp'' Hs]]].
    rewrite Hcl''. cbn. intros _ _.
    destruct (pasid_cache_lookup_tagged (pasid_cache_refill (pasid_cache_evict cache rid) (rid, pasid)
               e.(VtdPasid_s1_root)) rid pasid ec'' Hcl'') as [Hd'' Hp'''].
    repeat split; assumption.
  - reflexivity.
Qed.

(* Executable vector: evicting DID 0 then translating through the loop
   answers with the table hit and refills the cache. *)
Lemma test_vector_pasid_translate_fill_after_evict :
  pasid_translate_fill [vtd_pasid_hit_context] 0 [vtd_pasid_hit_entry]
    (pasid_cache_evict [vtd_coherent_cache_entry] 0) 0 mem_vtd_pasid_hit va0
  = (Some (expected_pa, Read),
     pasid_cache_refill (pasid_cache_evict [vtd_coherent_cache_entry] 0) (0, 0) vtd_s1_root).
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

(* ============================================================
   S4.5 device-table fill-on-miss: `vtd_device_translate_fill` is the
   translation service loop *over the device table* — a cache hit (keyed by
   the DTE's DID) walks the cached first-stage root, a miss re-walks the
   device's PASID table (selected by the DTE's `pasid_tbl` pointer), refills
   under (d.did, pasid), and walks.  The device-table analogue of
   `pasid_translate_fill`, with the tag taken from the DTE rather than the
   requester ID (VT-d 5.20 §15.4).
   ============================================================ *)

(* A hit: the cached two-stage walk, cache untouched. *)
Lemma vtd_device_translate_fill_hit (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (cache : list PasidCacheEntry)
    (mem : list MemEntry) (iova : mword 64) (d : VtdDeviceEntry) (ec : PasidCacheEntry) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_cache_lookup cache (d.(VtdDeviceEntry_did), pasid) = Some ec ->
  ec.(PasidCacheEntry_present) = true ->
  vtd_device_translate_fill devtbl tbls contexts rid pasid cache mem iova
  = (vtd_walk_device_pasid_cached devtbl tbls contexts rid pasid cache mem iova, cache).
Proof.
  intros Hd Hdp Hcl Hcp.
  unfold vtd_device_translate_fill. rewrite Hd. cbn. rewrite Hdp. cbn. rewrite Hcl. cbn.
  rewrite Hcp. cbn. reflexivity.
Qed.

(* A miss (non-present slot) with a present table entry re-walks the device's
   PASID table and refills the cache under the DTE's DID — not the requester
   ID — with the table's first-stage root. *)
Lemma vtd_device_translate_fill_miss_refills (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (cache : list PasidCacheEntry)
    (mem : list MemEntry) (iova : mword 64) (d : VtdDeviceEntry) (ec : PasidCacheEntry)
    (ptes : list VtdPasid) (te : VtdPasid) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_cache_lookup cache (d.(VtdDeviceEntry_did), pasid) = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = Some ptes ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = true ->
  vtd_device_translate_fill devtbl tbls contexts rid pasid cache mem iova
  = (vtd_walk_device_pasid devtbl tbls contexts rid pasid mem iova,
     pasid_cache_refill cache (d.(VtdDeviceEntry_did), pasid) te.(VtdPasid_s1_root)).
Proof.
  intros Hd Hdp Hcl Hcp Ht Hp Htp.
  unfold vtd_device_translate_fill. rewrite Hd. cbn. rewrite Hdp. cbn. rewrite Hcl. cbn.
  rewrite Hcp. cbn. rewrite Ht. cbn. rewrite Hp. cbn. rewrite Htp. cbn. reflexivity.
Qed.

(* A miss with no PASID table faults and leaves the cache alone. *)
Lemma vtd_device_translate_fill_miss_missing_table (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (cache : list PasidCacheEntry)
    (mem : list MemEntry) (iova : mword 64) (d : VtdDeviceEntry) (ec : PasidCacheEntry) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_cache_lookup cache (d.(VtdDeviceEntry_did), pasid) = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = None ->
  vtd_device_translate_fill devtbl tbls contexts rid pasid cache mem iova = (None, cache).
Proof.
  intros Hd Hdp Hcl Hcp Ht.
  unfold vtd_device_translate_fill. rewrite Hd. cbn. rewrite Hdp. cbn. rewrite Hcl. cbn.
  rewrite Hcp. cbn. rewrite Ht. cbn. reflexivity.
Qed.

(* A miss with a non-present table entry faults and leaves the cache alone. *)
Lemma vtd_device_translate_fill_miss_nonpresent_entry (devtbl : list VtdDeviceEntry)
    (tbls : list (list VtdPasid)) (contexts : list VtdContext) (rid pasid : Z)
    (cache : list PasidCacheEntry) (mem : list MemEntry) (iova : mword 64)
    (d : VtdDeviceEntry) (ec : PasidCacheEntry) (ptes : list VtdPasid) (te : VtdPasid) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_cache_lookup cache (d.(VtdDeviceEntry_did), pasid) = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = Some ptes ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = false ->
  vtd_device_translate_fill devtbl tbls contexts rid pasid cache mem iova = (None, cache).
Proof.
  intros Hd Hdp Hcl Hcp Ht Hp Htp.
  unfold vtd_device_translate_fill. rewrite Hd. cbn. rewrite Hdp. cbn. rewrite Hcl. cbn.
  rewrite Hcp. cbn. rewrite Ht. cbn. rewrite Hp. cbn. rewrite Htp. cbn. reflexivity.
Qed.

(* After an eviction (of the DTE's DID) the device-table loop recovers: it
   re-walks the device's PASID table and refills under the DTE's DID, so it
   answers with the device-table walk result — the invalidation-then-
   retranslate cycle over the device table. *)
Theorem vtd_device_translate_fill_after_evict (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (cache : list PasidCacheEntry)
    (mem : list MemEntry) (iova : mword 64) (d : VtdDeviceEntry) (ec : PasidCacheEntry)
    (ptes : list VtdPasid) (te : VtdPasid) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_cache_lookup cache (d.(VtdDeviceEntry_did), pasid) = Some ec ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = Some ptes ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = true ->
  vtd_device_translate_fill devtbl tbls contexts rid pasid (pasid_cache_evict cache d.(VtdDeviceEntry_did)) mem iova
  = (vtd_walk_device_pasid devtbl tbls contexts rid pasid mem iova,
     pasid_cache_refill (pasid_cache_evict cache d.(VtdDeviceEntry_did)) (d.(VtdDeviceEntry_did), pasid)
       te.(VtdPasid_s1_root)).
Proof.
  intros Hd Hdp Hcl Ht Hp Htp.
  destruct (pasid_cache_evict_lookup cache d.(VtdDeviceEntry_did) pasid ec Hcl) as [ec' [Hev Hpev]].
  apply (vtd_device_translate_fill_miss_refills devtbl tbls contexts rid pasid
           (pasid_cache_evict cache d.(VtdDeviceEntry_did)) mem iova d ec' ptes te
           Hd Hdp Hev Hpev Ht Hp Htp).
Qed.

(* The device-table loop's refill carries the DTE's DID — the cache is keyed
   by (d.did, pasid), so the refilled entry is findable under the DTE's tag. *)
Lemma vtd_device_translate_fill_refill_tagged (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid : Z) (cache : list PasidCacheEntry)
    (mem : list MemEntry) (iova : mword 64) (d : VtdDeviceEntry) (ec : PasidCacheEntry)
    (ptes : list VtdPasid) (te : VtdPasid) :
  vtd_device_lookup devtbl rid = Some d ->
  d.(VtdDeviceEntry_present) = true ->
  pasid_cache_lookup cache (d.(VtdDeviceEntry_did), pasid) = Some ec ->
  ec.(PasidCacheEntry_present) = false ->
  pasid_table_lookup tbls d.(VtdDeviceEntry_pasid_tbl) = Some ptes ->
  vtd_pasid_lookup ptes pasid = Some te ->
  te.(VtdPasid_present) = true ->
  exists ec',
    pasid_cache_lookup (snd (vtd_device_translate_fill devtbl tbls contexts rid pasid cache mem iova))
                       (d.(VtdDeviceEntry_did), pasid) = Some ec' /\
    ec'.(PasidCacheEntry_present) = true /\
    ec'.(PasidCacheEntry_did) = d.(VtdDeviceEntry_did) /\
    ec'.(PasidCacheEntry_pasid) = pasid /\
    ec'.(PasidCacheEntry_s1_root) = te.(VtdPasid_s1_root).
Proof.
  intros Hd Hdp Hcl Hcp Ht Hp Htp.
  rewrite (vtd_device_translate_fill_miss_refills devtbl tbls contexts rid pasid cache mem iova
            d ec ptes te Hd Hdp Hcl Hcp Ht Hp Htp).
  cbn.
  destruct (pasid_cache_refill_lookup cache d.(VtdDeviceEntry_did) pasid te.(VtdPasid_s1_root) ec Hcl)
    as [ec' [Hcl' [Hp' Hs]]].
  exists ec'. split; [exact Hcl' |].
  destruct (pasid_cache_lookup_tagged (pasid_cache_refill cache (d.(VtdDeviceEntry_did), pasid)
             te.(VtdPasid_s1_root)) d.(VtdDeviceEntry_did) pasid ec' Hcl') as [Hd' Hp''].
  repeat split; assumption.
Qed.

(* Executable vectors over the device table: a cached hit (cache keyed by the
   DTE's DID 7) resolves the two-stage walk; after an eviction of DID 7 the
   loop recovers via the PASID-table walk + refill under (7, 0). *)
Definition vtd_dev_coherent_cache_entry : PasidCacheEntry :=
  {| PasidCacheEntry_present := true; PasidCacheEntry_did := 7; PasidCacheEntry_pasid := 0; PasidCacheEntry_gen := 0;
     PasidCacheEntry_s1_root := vtd_s1_root |}.

Lemma test_vector_vtd_device_translate_fill_hit :
  vtd_device_translate_fill [vtd_dev_pasid_hit_entry] [ [vtd_pasid_hit_entry] ] [vtd_pasid_hit_context]
    0 0 [vtd_dev_coherent_cache_entry] mem_vtd_pasid_hit va0
  = (Some (expected_pa, Read), [vtd_dev_coherent_cache_entry]).
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_vtd_device_translate_fill_after_evict :
  vtd_device_translate_fill [vtd_dev_pasid_hit_entry] [ [vtd_pasid_hit_entry] ] [vtd_pasid_hit_context]
    0 0 (pasid_cache_evict [vtd_dev_coherent_cache_entry] 7) mem_vtd_pasid_hit va0
  = (Some (expected_pa, Read),
     pasid_cache_refill (pasid_cache_evict [vtd_dev_coherent_cache_entry] 7) (7, 0) vtd_s1_root).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.5 FRCDR drain-by-software: software reads the head of the FRCD queue
   (the oldest recorded fault), clears it, and drains the whole queue — after
   which the interrupt line deasserts and the interrupt controller sees a
   no-op.  This is the software half of VT-d fault handling (5.20 §6.1): the
   fault is recorded (raising the line), the handler drains it to learn which
   endpoint / address faulted, and the line comes back down.
   ============================================================ *)

(* The head of the queue is the fault just recorded. *)
Lemma frcd_head_record (fr : FaultRecord) (cache : list FrcdEntry) :
  frcd_head (frcd_record fr cache) = Some (frcd_of fr).
Proof. cbn. reflexivity. Qed.

(* Clearing the head of a freshly-recorded fault empties the queue. *)
Lemma frcd_clear_record_empty (fr : FaultRecord) :
  frcd_clear (frcd_record fr []) = [].
Proof. cbn. reflexivity. Qed.

(* After clearing the recorded fault the interrupt line deasserts: no
   outstanding fault, no pending interrupt. *)
Lemma frcd_clear_deasserts (fr : FaultRecord) :
  frcd_pending (frcd_clear (frcd_record fr [])) = false.
Proof. cbn. reflexivity. Qed.

(* Draining the whole queue clears it — for any FRCD contents. *)
Lemma frcd_drain_clears (cache : list FrcdEntry) :
  frcd_drain cache = [].
Proof. induction cache as [| e rest IH]; cbn; [reflexivity | exact IH]. Qed.

(* ... so the line deasserts after a full drain. *)
Lemma frcd_drain_deasserts (cache : list FrcdEntry) :
  frcd_pending (frcd_drain cache) = false.
Proof. rewrite frcd_drain_clears. cbn. reflexivity. Qed.

(* ... and the interrupt controller sees a no-op: with the queue drained there
   is nothing to signal. *)
Lemma frcd_drain_recovers (cache : list FrcdEntry) (ic : intc_types.Intc) (core : Z) :
  frcd_signal_intc (frcd_drain cache) ic core = ic.
Proof. rewrite frcd_drain_clears. apply frcd_signal_drained_noop. cbn. reflexivity. Qed.

(* The full drain cycle: record a fault, learn it from the head, drain — the
   line is back down and the fault message names the faulting endpoint. *)
Theorem frcd_drain_cycle (fr : FaultRecord) :
  frcd_head (frcd_record fr []) = Some (frcd_of fr) /\
  fault_msg_did_pasid (frcd_of fr) = (FaultRecord_did fr, FaultRecord_pasid fr) /\
  frcd_pending (frcd_drain (frcd_record fr [])) = false.
Proof. cbn. repeat split; reflexivity. Qed.

(* Executable vector: record a stage-2 fault for (0, 3, va0), learn it from
   the head, drain — the line deasserts. *)
Lemma test_vector_frcd_drain :
  frcd_head (frcd_record {| FaultRecord_did := 0; FaultRecord_pasid := 3; FaultRecord_iova := va0;
                            FaultRecord_reason := FR_Stage2Fault |} [])
  = Some {| FrcdEntry_did := 0; FrcdEntry_pasid := 3; FrcdEntry_iova := va0;
           FrcdEntry_reason := FR_Stage2Fault |} /\
  frcd_pending (frcd_drain (frcd_record {| FaultRecord_did := 0; FaultRecord_pasid := 3;
                                          FaultRecord_iova := va0;
                                          FaultRecord_reason := FR_Stage2Fault |} [])) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================
   S4.5 PRI × FRCD composition: a *pending* page request's translation fault
   delivers the fault record (DID, PASID, IOVA, reason), which the FRCD
   records — raising the fault-message interrupt whose payload names the
   faulting endpoint (VT-d 5.20 §7.2).  Once the kernel resolves the request
   (`pri_resolve`) the pending bit clears, so no further record is produced
   and the device's retried ATS translation proceeds (PCIe ATS §4.2).
   ============================================================ *)

(* The pending-bit fault path records into the FRCD: the record is produced,
   findable at the head, and raises the line with the (did, pasid) message. *)
Lemma pri_fault_frcd_records (q : list PriRequest) (did pasid : Z) (iova : mword 64) (reason : FaultReason) :
  pri_pending q (did, pasid) iova = true ->
  exists fr : FaultRecord,
    pri_fault_delivers q (did, pasid) iova reason = Some fr /\
    frcd_head (frcd_record fr []) = Some (frcd_of fr) /\
    frcd_pending (frcd_record fr []) = true /\
    fault_msg_did_pasid (frcd_of fr) = (did, pasid).
Proof.
  intros Hp.
  exists {| FaultRecord_did := did; FaultRecord_pasid := pasid; FaultRecord_iova := iova;
           FaultRecord_reason := reason |}.
  rewrite (pri_fault_delivers_pending q did pasid iova reason Hp).
  split; [reflexivity |].
  split; [apply frcd_head_record |].
  split; [apply frcd_record_signals |].
  rewrite fault_msg_of_record. cbn. reflexivity.
Qed.

(* After the kernel mapped the page, the retry produces no fault record — the
   request is resolved, so the fault-message path is silent. *)
Lemma pri_fault_frcd_after_resolve_silent (q : list PriRequest) (did pasid : Z) (iova : mword 64)
    (reason : FaultReason) :
  pri_fault_delivers (pri_resolve q (did, pasid) iova) (did, pasid) iova reason = None.
Proof.
  apply pri_fault_delivers_none. apply pri_resolve_clears.
Qed.

(* Executable vector: request (0, 0, va0) → pending → the fault delivers the
   record, the FRCD raises the line; resolve → no record. *)
Lemma test_vector_pri_fault_frcd :
  let q := pri_request [] (0, 0) va0 in
  pri_pending q (0, 0) va0 = true /\
  pri_fault_delivers q (0, 0) va0 FR_Stage2Fault
  = Some {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := va0;
           FaultRecord_reason := FR_Stage2Fault |} /\
  frcd_pending (frcd_record {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := va0;
                               FaultRecord_reason := FR_Stage2Fault |} []) = true /\
  pri_fault_delivers (pri_resolve q (0, 0) va0) (0, 0) va0 FR_Stage2Fault = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================
   S4.5 PRI fault -> INTC delivery: the device-side fault-message chain — a
   *pending* page request's translation fault delivers the record into the
   FRCD, which raises the fault line on the target core (the twin of
   `vtd_shootdown_frcd_delivers`, driven by the pending bit rather than the
   queue shootdown), and the kernel's unmasked, delivery-enabled ack rings the
   doorbell.  Once the kernel maps the page the request is resolved, so the
   path is silent: no record, no line.
   ============================================================ *)

(* The full device-side chain: pending request -> fault record -> FRCD ->
   line raised on the target core, with the (did, pasid) fault message. *)
Theorem pri_fault_frcd_delivers_intc (q : list PriRequest) (did pasid : Z) (iova : mword 64)
    (reason : FaultReason) (ic : intc_types.Intc) (core : nat) :
  pri_pending q (did, pasid) iova = true ->
  Nat.lt core (length (intc_types.Intc_pending ic)) ->
  exists fr : FaultRecord,
    pri_fault_delivers q (did, pasid) iova reason = Some fr /\
    fault_msg_did_pasid (frcd_of fr) = (did, pasid) /\
    intc.intc_get_bit (intc_types.Intc_pending
                         (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core)))
      (Z.of_nat core) false = true.
Proof.
  intros Hp Hlen.
  destruct (pri_fault_frcd_records q did pasid iova reason Hp) as [fr [Hdel [Hhead [Hpend Hmsg]]]].
  exists fr. split; [exact Hdel |]. split; [exact Hmsg |].
  apply (frcd_signal_raises (frcd_record fr []) ic core Hlen Hpend).
Qed.

(* ... and the kernel's ack of the raised line rings the doorbell: the
   device-side twin of `vtd_fault_ack_rings`. *)
Lemma pri_fault_frcd_ack_rings (q : list PriRequest) (did pasid : Z) (iova : mword 64)
    (reason : FaultReason) (ic : intc_types.Intc) (core : nat) :
  pri_pending q (did, pasid) iova = true ->
  intc.intc_get_bit (intc_types.Intc_masked ic) (Z.of_nat core) false = false ->
  intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat core) false = true ->
  Nat.lt core (length (intc_types.Intc_pending ic)) ->
  exists fr : FaultRecord,
    pri_fault_delivers q (did, pasid) iova reason = Some fr /\
    intc_types.Intc_ipi (intc.intc_ack (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core))
                                       (Z.of_nat core))
    = intc.intc_set_bit (intc_types.Intc_ipi ic) (Z.of_nat core) true.
Proof.
  intros Hp Hm Hd Hlen.
  destruct (pri_fault_frcd_records q did pasid iova reason Hp) as [fr [Hdel [Hhead [Hpend Hmsg]]]].
  exists fr. split; [exact Hdel |].
  apply (vtd_fault_ack_rings (frcd_record fr []) ic core Hpend Hm Hd Hlen).
Qed.

(* Once the kernel mapped the page, the request is resolved and the fault path
   is silent: no record is delivered, and with nothing recorded the INTC is
   untouched. *)
Lemma pri_fault_frcd_resolved_silent (q : list PriRequest) (did pasid : Z) (iova : mword 64)
    (reason : FaultReason) (ic : intc_types.Intc) (core : Z) :
  pri_fault_delivers (pri_resolve q (did, pasid) iova) (did, pasid) iova reason = None /\
  frcd_signal_intc [] ic core = ic.
Proof.
  split.
  - apply pri_fault_frcd_after_resolve_silent.
  - cbn. reflexivity.
Qed.

(* Executable vector: a pending request's fault raises the line on core 0 and
   the kernel's ack rings the doorbell — the device-side twin of the
   shootdown-driven vector. *)
Lemma test_vector_pri_fault_frcd_delivers_intc :
  let q := pri_request [] (0, 0) va0 in
  pri_pending q (0, 0) va0 = true /\
  intc.intc_get_bit (intc_types.Intc_pending
                       (frcd_signal_intc (frcd_record {| FaultRecord_did := 0; FaultRecord_pasid := 0;
                                                         FaultRecord_iova := va0;
                                                         FaultRecord_reason := FR_Stage2Fault |} [])
                                         vtd_intc0 0))
    0 false = true /\
  intc_types.Intc_ipi
    (intc.intc_ack (frcd_signal_intc (frcd_record {| FaultRecord_did := 0; FaultRecord_pasid := 0;
                                                     FaultRecord_iova := va0;
                                                     FaultRecord_reason := FR_Stage2Fault |} [])
                                      vtd_intc0 0) 0)
  = [true].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================
   S4.5 PASID-cache generation tags (VT-d 5.20 §15.4): the PASID cache tag is
   (DID, PASID, generation).  The generation distinguishes reuses of a
   (DID, PASID) tag across address-space teardown: a transaction issued under
   the *current* generation g must not hit a stale-generation entry
   (`pasid_cache_lookup_gen` misses it), the hardware detects the reuse as a
   *tag conflict* (`pasid_cache_tag_conflict` — a present entry for the tag
   whose generation is stale), software evicts the conflict
   (`pasid_cache_evict_gen` — clear exactly the stale-generation entries of
   the reused tag, leaving a fresh-generation entry and other tags alone),
   and refill re-installs the root under the *current* generation
   (`pasid_cache_refill_gen`), after which no conflict remains.
   ============================================================ *)

(* Refill under the current generation g makes the gen-tagged lookup hit: the
   entry is present, carries g, and the fresh root. *)
Lemma pasid_cache_lookup_gen_installs (cache : list PasidCacheEntry) (d p g : Z) (root : mword 44) :
  pasid_cache_lookup_gen (pasid_cache_refill_gen cache (d, p) g root) (d, p) g
  = Some {| PasidCacheEntry_present := true; PasidCacheEntry_did := d; PasidCacheEntry_pasid := p;
           PasidCacheEntry_gen := g; PasidCacheEntry_s1_root := root |}.
Proof.
  revert d p g. induction cache as [| e rest IH]; cbn; intros d p g.
  - rewrite (proj2 (Z.eqb_eq _ _) eq_refl), (proj2 (Z.eqb_eq _ _) eq_refl),
            (proj2 (Z.eqb_eq _ _) eq_refl). cbn. reflexivity.
  - destruct (Z.eqb_spec e.(PasidCacheEntry_did) d) as [Hd | Hd]; cbn.
    + destruct (Z.eqb_spec e.(PasidCacheEntry_pasid) p) as [Hp | Hp]; cbn.
      * rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp), (proj2 (Z.eqb_eq _ _) eq_refl). cbn.
        rewrite Hd, Hp. reflexivity.
      * rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH d p g).
    + rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH d p g).
Qed.

(* A stale-generation entry never answers the current-generation lookup: the
   full tag (DID, PASID, gen) no longer matches, so the access misses. *)
Lemma pasid_cache_lookup_gen_stale_singleton (e : PasidCacheEntry) (g : Z) :
  e.(PasidCacheEntry_gen) <> g ->
  pasid_cache_lookup_gen [e] (e.(PasidCacheEntry_did), e.(PasidCacheEntry_pasid)) g = None.
Proof.
  intros Hgen. cbn.
  rewrite (proj2 (Z.eqb_eq _ _) eq_refl), (proj2 (Z.eqb_eq _ _) eq_refl).
  rewrite (proj2 (Z.eqb_neq _ _) Hgen). cbn. reflexivity.
Qed.

(* Tag-conflict eviction turns the stale-generation entries of the reused tag
   non-present: the (DID, PASID) lookup under the *old* generation finds the
   slot, but it no longer holds a usable root. *)
Lemma pasid_cache_evict_gen_clears_present (cache : list PasidCacheEntry) (d p g g0 : Z) (e : PasidCacheEntry) :
  g0 <> g ->
  pasid_cache_lookup_gen cache (d, p) g0 = Some e ->
  exists e', pasid_cache_lookup_gen (pasid_cache_evict_gen cache (d, p) g) (d, p) g0 = Some e' /\
             e'.(PasidCacheEntry_present) = false.
Proof.
  revert d p g g0. induction cache as [| h rest IH]; cbn; intros d p g g0 Hneq H.
  - discriminate.
  - destruct (Z.eqb_spec h.(PasidCacheEntry_did) d) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) p) as [Hp | Hp]; cbn in H.
      * destruct (Z.eqb_spec h.(PasidCacheEntry_gen) g0) as [Hg0 | Hg0]; cbn in H.
        -- (* the lookup found h at the old generation; h.gen = g0 <> g, so the
              eviction clears it. *)
           injection H as <-.
           assert (Hhg : h.(PasidCacheEntry_gen) <> g) by congruence.
           exists {| PasidCacheEntry_present := false; PasidCacheEntry_did := h.(PasidCacheEntry_did);
                    PasidCacheEntry_pasid := h.(PasidCacheEntry_pasid);
                    PasidCacheEntry_gen := h.(PasidCacheEntry_gen);
                    PasidCacheEntry_s1_root := h.(PasidCacheEntry_s1_root) |}.
           cbn. unfold machine.neq_int.
           rewrite (proj2 (Z.eqb_neq _ _) Hhg). cbn.
           rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp),
                   (proj2 (Z.eqb_eq _ _) Hg0). cbn. split; reflexivity.
        -- (* h.gen <> g0: the lookup skips the head; the eviction either
              clears it (h.gen <> g) or keeps it (h.gen = g) — either way the
              (d, p) @ g0 lookup moves to the tail. *)
           destruct (Z.eqb_spec h.(PasidCacheEntry_gen) g) as [Hg | Hg]; cbn.
           ++ cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_eq _ _) Hg). cbn.
              rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp),
                      (proj2 (Z.eqb_neq _ _) Hg0). cbn. exact (IH d p g g0 Hneq H).
           ++ cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_neq _ _) Hg). cbn.
              rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp),
                      (proj2 (Z.eqb_neq _ _) Hg0). cbn. exact (IH d p g g0 Hneq H).
      * cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH d p g g0 Hneq H).
    + cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH d p g g0 Hneq H).
Qed.

(* A fresh-generation entry (gen = g) survives the tag-conflict eviction:
   only stale generations of the reused tag are cleared. *)
Lemma pasid_cache_evict_gen_preserves_fresh (cache : list PasidCacheEntry) (d p g : Z) (e : PasidCacheEntry) :
  pasid_cache_lookup_gen cache (d, p) g = Some e ->
  pasid_cache_lookup_gen (pasid_cache_evict_gen cache (d, p) g) (d, p) g = Some e.
Proof.
  revert d p g. induction cache as [| h rest IH]; cbn; intros d p g H.
  - discriminate.
  - destruct (Z.eqb_spec h.(PasidCacheEntry_did) d) as [Hd | Hd]; cbn in H.
    + destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) p) as [Hp | Hp]; cbn in H.
      * destruct (Z.eqb_spec h.(PasidCacheEntry_gen) g) as [Hg | Hg]; cbn in H.
        -- (* h is the fresh entry itself: eviction keeps it (gen = g), and the
              lookup still finds it. *)
           injection H as <-.
           cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_eq _ _) Hg). cbn.
           rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp),
                   (proj2 (Z.eqb_eq _ _) Hg). cbn. reflexivity.
        -- (* h matches (d,p) with gen <> g: the current-generation lookup skips
              it, eviction clears it, and the lookup still skips it. *)
           cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_neq _ _) Hg). cbn.
           rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp),
                   (proj2 (Z.eqb_neq _ _) Hg). cbn. exact (IH d p g H).
      * cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH d p g H).
    + cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH d p g H).
Qed.

(* Tag-conflict eviction is selective per tag: entries under any other DID (or
   any other PASID) survive untouched, findable at their own generation. *)
Lemma pasid_cache_evict_gen_preserves_other_did (cache : list PasidCacheEntry) (d d' p p' g g' : Z) :
  d <> d' ->
  forall e, pasid_cache_lookup_gen cache (d', p') g' = Some e ->
         pasid_cache_lookup_gen (pasid_cache_evict_gen cache (d, p) g) (d', p') g' = Some e.
Proof.
  revert d p g d' p' g'. induction cache as [| h rest IH]; cbn; intros d p g d' p' g' Hneq e H.
  - discriminate.
  - destruct (Z.eqb_spec h.(PasidCacheEntry_did) d) as [Hd | Hd]; cbn in H.
    + (* h.did = d — the eviction may clear h, but the target tag is (d', p')
         with d <> d', so the gen-tagged lookup skips h either way. *)
      assert (Hhead : Z.eqb h.(PasidCacheEntry_did) d' = false).
      { apply Z.eqb_neq. intros Hsub. apply Hneq. congruence. }
      destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) p) as [Hp | Hp]; cbn in H.
      * destruct (Z.eqb_spec h.(PasidCacheEntry_gen) g) as [Hg | Hg]; cbn in H.
        -- rewrite Hhead in H. cbn in H.
           cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_eq _ _) Hg). cbn.
           rewrite Hhead. cbn. exact (IH d p g d' p' g' Hneq e H).
        -- rewrite Hhead in H. cbn in H.
           cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_neq _ _) Hg). cbn.
           rewrite Hhead. cbn. exact (IH d p g d' p' g' Hneq e H).
      * rewrite Hhead in H. cbn in H.
        cbn. rewrite Hhead. cbn. exact (IH d p g d' p' g' Hneq e H).
    + (* h.did <> d — the eviction keeps h untouched. *)
      destruct (Z.eqb_spec h.(PasidCacheEntry_did) d') as [Hd' | Hd']; cbn in H.
      * destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) p') as [Hp' | Hp']; cbn in H.
        -- destruct (Z.eqb_spec h.(PasidCacheEntry_gen) g') as [Hg' | Hg']; cbn in H.
           ++ cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd'), (proj2 (Z.eqb_eq _ _) Hp'),
                           (proj2 (Z.eqb_eq _ _) Hg'). cbn. exact H.
           ++ cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd'), (proj2 (Z.eqb_eq _ _) Hp'),
                           (proj2 (Z.eqb_neq _ _) Hg'). cbn. exact (IH d p g d' p' g' Hneq e H).
        -- cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd'), (proj2 (Z.eqb_neq _ _) Hp'). cbn. exact (IH d p g d' p' g' Hneq e H).
      * cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd'). cbn. exact (IH d p g d' p' g' Hneq e H).
Qed.

(* After the tag-conflict eviction no conflict remains at the current
   generation: every *present* (DID, PASID) entry carries the current gen. *)
Lemma pasid_cache_evict_gen_conflict_free (cache : list PasidCacheEntry) (d p g : Z) :
  pasid_cache_tag_conflict (pasid_cache_evict_gen cache (d, p) g) (d, p) g = false.
Proof.
  revert d p g. induction cache as [| h rest IH]; cbn; intros d p g.
  - reflexivity.
  - destruct (Z.eqb_spec h.(PasidCacheEntry_did) d) as [Hd | Hd]; cbn.
    + destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) p) as [Hp | Hp]; cbn.
      * destruct h.(PasidCacheEntry_present) eqn:Hp0; cbn.
        -- destruct (Z.eqb_spec h.(PasidCacheEntry_gen) g) as [Hg | Hg]; cbn.
           ++ (* h is present and current: eviction keeps it; the conflict scan
                sees a present entry at the current gen and moves to the tail. *)
              cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_eq _ _) Hg). cbn.
              rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp), Hp0. cbn.
              rewrite (proj2 (Z.eqb_eq _ _) Hg). cbn. exact (IH d p g).
           ++ (* h is present but stale: the eviction clears it; the conflict
                scan skips the non-present head and moves to the tail. *)
              cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_neq _ _) Hg). cbn.
              rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp). cbn. exact (IH d p g).
        -- destruct (Z.eqb_spec h.(PasidCacheEntry_gen) g) as [Hg | Hg]; cbn.
           ++ cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_eq _ _) Hg). cbn.
              rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp), Hp0. cbn. exact (IH d p g).
           ++ cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_neq _ _) Hg). cbn.
              rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp). cbn. exact (IH d p g).
      * rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH d p g).
    + rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH d p g).
Qed.

(* Evicting the conflict and refilling under the current generation leaves no
   conflict: the reused tag is present with the current gen, and every other
   entry for the tag was cleared (non-present) by the eviction. *)
Lemma pasid_cache_refill_gen_conflict_free (cache : list PasidCacheEntry) (d p g : Z) (root : mword 44) :
  pasid_cache_tag_conflict
    (pasid_cache_refill_gen (pasid_cache_evict_gen cache (d, p) g) (d, p) g root) (d, p) g = false.
Proof.
  revert d p g. induction cache as [| h rest IH]; cbn; intros d p g.
  - rewrite (proj2 (Z.eqb_eq _ _) eq_refl), (proj2 (Z.eqb_eq _ _) eq_refl),
            (proj2 (Z.eqb_eq _ _) eq_refl). cbn. reflexivity.
  - destruct (Z.eqb_spec h.(PasidCacheEntry_did) d) as [Hd | Hd]; cbn.
    + destruct (Z.eqb_spec h.(PasidCacheEntry_pasid) p) as [Hp | Hp]; cbn.
      * (* the head is the reused tag: after evict + refill it carries the
           current gen, and the tail is just the evicted rest — conflict-free
           by pasid_cache_evict_gen_conflict_free. *)
        destruct (Z.eqb_spec h.(PasidCacheEntry_gen) g) as [Hg | Hg]; cbn.
        -- cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_eq _ _) Hg). cbn.
           rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp). cbn.
           rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp),
                   (proj2 (Z.eqb_eq _ _) eq_refl). cbn.
           exact (pasid_cache_evict_gen_conflict_free rest d p g).
        -- cbn. unfold machine.neq_int. rewrite (proj2 (Z.eqb_neq _ _) Hg). cbn.
           rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp). cbn.
           rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_eq _ _) Hp),
                   (proj2 (Z.eqb_eq _ _) eq_refl). cbn.
           exact (pasid_cache_evict_gen_conflict_free rest d p g).
      * cbn. rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn.
        rewrite (proj2 (Z.eqb_eq _ _) Hd), (proj2 (Z.eqb_neq _ _) Hp). cbn. exact (IH d p g).
    + cbn. rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn.
      rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn. exact (IH d p g).
Qed.

(* The tag-conflict recovery cycle: evict the stale generation, refill under
   the current one — the current-generation lookup hits the fresh root and no
   conflict remains. *)
Lemma pasid_cache_evict_gen_refill_cycle (cache : list PasidCacheEntry) (d p g : Z) (root : mword 44) :
  pasid_cache_lookup_gen (pasid_cache_refill_gen (pasid_cache_evict_gen cache (d, p) g) (d, p) g root) (d, p) g
  = Some {| PasidCacheEntry_present := true; PasidCacheEntry_did := d; PasidCacheEntry_pasid := p;
           PasidCacheEntry_gen := g; PasidCacheEntry_s1_root := root |} /\
  pasid_cache_tag_conflict (pasid_cache_refill_gen (pasid_cache_evict_gen cache (d, p) g) (d, p) g root) (d, p) g = false.
Proof.
  split.
  - apply pasid_cache_lookup_gen_installs.
  - apply pasid_cache_refill_gen_conflict_free.
Qed.

(* Executable vector: the two-generation tag-conflict cycle — a gen-0 entry is
   stale under the current gen 1, the conflict is detected, evicted, and
   refilled under gen 1, after which the current-generation lookup hits the
   fresh root and no conflict remains. *)
Lemma test_vector_pasid_cache_generation :
  let cache := [{| PasidCacheEntry_present := true; PasidCacheEntry_did := 0; PasidCacheEntry_pasid := 0;
                  PasidCacheEntry_gen := 0; PasidCacheEntry_s1_root := vtd_s1_root |}] in
  pasid_cache_lookup_gen cache (0, 0) 1 = None /\
  pasid_cache_tag_conflict cache (0, 0) 1 = true /\
  pasid_cache_lookup_gen (pasid_cache_evict_gen cache (0, 0) 1) (0, 0) 0
  = Some {| PasidCacheEntry_present := false; PasidCacheEntry_did := 0; PasidCacheEntry_pasid := 0;
           PasidCacheEntry_gen := 0; PasidCacheEntry_s1_root := vtd_s1_root |} /\
  pasid_cache_lookup_gen (pasid_cache_refill_gen (pasid_cache_evict_gen cache (0, 0) 1) (0, 0) 1 vtd_s1_root) (0, 0) 1
  = Some {| PasidCacheEntry_present := true; PasidCacheEntry_did := 0; PasidCacheEntry_pasid := 0;
           PasidCacheEntry_gen := 1; PasidCacheEntry_s1_root := vtd_s1_root |} /\
  pasid_cache_tag_conflict (pasid_cache_refill_gen (pasid_cache_evict_gen cache (0, 0) 1) (0, 0) 1 vtd_s1_root) (0, 0) 1 = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

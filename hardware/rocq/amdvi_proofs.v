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
Require Import coherence.      (* remove_entry *)
Require Import coherence_leaf. (* unmap_leaf_mem, read_pte_remove_other, leaf_addr *)
Require Import iommu_proofs.   (* iommu_unmap_faults, iotlb_invalidate_removes *)
Require Import machine_encoding. (* invalid_pte (test vectors) *)
Require Import conformance.    (* oracle_walk, translate_conforms *)
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

(* ============================================================
   S4.4 conformance vectors (non-empty): a full 4-level HIT (level-3 + the
   bottom 3 levels) and the level-3 fault cases, pinned against AMD-Vi §2.4
   (device table + I/O page table: 52-bit GPA, 4 x 9-bit levels + 12-bit
   offset).
   ============================================================ *)

(* The level-3 table root (distinct from the 3-level table's root_ppn). *)
Definition amd_root : mword 44 := mword_of_int 7.

(* Level-3 resolves to a valid non-leaf non-NAPOT PTE at root_ppn; the bottom 3
   levels are table_ok (va0 -> expected_pa). *)
Definition table_amd_hit : PageTable :=
  {| MemEntry_addr := pte_address amd_root (vpn3 va0); MemEntry_pte := ptr_pte root_ppn |} :: table_ok.

Lemma test_vector_amdvi_4level_hit :
  amdvi_walk amd_root table_amd_hit va0 = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* An invalid level-3 PTE faults (no I/O page-table root to use). *)
Definition table_amd_invalid_l3 : PageTable :=
  [ {| MemEntry_addr := pte_address amd_root (vpn3 va0); MemEntry_pte := invalid_pte |} ].

Lemma test_vector_amdvi_4level_invalid_l3 :
  amdvi_walk amd_root table_amd_invalid_l3 va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* A leaf level-3 PTE faults (the 4-level walk has no level-3 leaf). *)
Definition table_amd_leaf_l3 : PageTable :=
  [ {| MemEntry_addr := pte_address amd_root (vpn3 va0); MemEntry_pte := ro_pte root_ppn |} ].

Lemma test_vector_amdvi_4level_leaf_l3 :
  amdvi_walk amd_root table_amd_leaf_l3 va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* A NAPOT level-3 PTE faults (N=1 is reserved on a non-leaf pointer). *)
Definition table_amd_napot_l3 : PageTable :=
  [ {| MemEntry_addr := pte_address amd_root (vpn3 va0); MemEntry_pte := napot_pte root_ppn |} ].

Lemma test_vector_amdvi_4level_napot_l3 :
  amdvi_walk amd_root table_amd_napot_l3 va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.4 coherence replay: unmap + invalidate faults the 4-level walk.

   The AMD-Vi coherence twin of iommu_proofs.iommu_unmap_faults: removing the
   leaf PTE for an IOVA faults the 4-level walk.  The one extra ingredient over
   the 3-level case is that the level-3 PTE (the walk's top step) must survive
   the leaf removal — i.e. the level-3 slot `pte_address root (vpn3 iova)`
   differs from the removed leaf slot `a`.  [leaf_addr ... = Some a] pins which
   slot the unmap removes; the inequality is the alias-free premise.  (The
   full forest condition wf_page_table implies it at the platform level.)
   ============================================================ *)

(* Unmap faults the 4-level walk: the level-3 PTE survives the leaf removal
   (its slot differs), the 4-level walk refines the 3-level walk re-rooted at
   p3.ppn, and that walk faults after the unmap. *)
Lemma amdvi_unmap_faults (root : mword 44) (mem : list MemEntry) (iova : mword 64)
    (p3 : Pte) (a : mword 56) :
  leaf_addr (core_with_root p3.(Pte_ppn)) mem iova = Some a ->
  read_pte mem (pte_address root (vpn3 iova)) = Some p3 ->
  p3.(Pte_valid) = true ->
  is_leaf p3 = false ->
  p3.(Pte_napot) = false ->
  pte_address root (vpn3 iova) <> a ->
  amdvi_walk root (unmap_leaf_mem (core_with_root p3.(Pte_ppn)) mem iova) iova = None.
Proof.
  intros Ha Hr Hv Hl Hn Hne.
  assert (Hunmap : unmap_leaf_mem (core_with_root p3.(Pte_ppn)) mem iova = remove_entry mem a).
  { unfold unmap_leaf_mem. rewrite Ha. reflexivity. }
  rewrite Hunmap.
  assert (Hne' : a <> pte_address root (vpn3 iova)).
  { intro H. apply Hne. symmetry. exact H. }
  assert (Hsurv : read_pte (remove_entry mem a) (pte_address root (vpn3 iova)) = Some p3).
  { rewrite (read_pte_remove_other mem a (pte_address root (vpn3 iova)) Hne'). exact Hr. }
  rewrite (amdvi_walk_refines_iommu_walk root (remove_entry mem a) iova p3 Hsurv Hv Hl Hn).
  rewrite <- Hunmap. apply (iommu_unmap_faults p3.(Pte_ppn) mem iova).
Qed.

(* The correct AMD-Vi unmap: the mapping is gone (the 4-level walk faults) AND
   no cached device translation for the freed frame survives the invalidation
   (the AMD-Vi twin of iommu_proofs.iommu_unmap_correct). *)
Lemma amdvi_unmap_correct (root : mword 44) (mem : list MemEntry) (iova : mword 64)
    (p3 : Pte) (a : mword 56) (iotlb : list IotlbEntry) :
  leaf_addr (core_with_root p3.(Pte_ppn)) mem iova = Some a ->
  read_pte mem (pte_address root (vpn3 iova)) = Some p3 ->
  p3.(Pte_valid) = true ->
  is_leaf p3 = false ->
  p3.(Pte_napot) = false ->
  pte_address root (vpn3 iova) <> a ->
  amdvi_walk root (unmap_leaf_mem (core_with_root p3.(Pte_ppn)) mem iova) iova = None /\
  Forall (fun e => vpn_of e.(IotlbEntry_iova) <> vpn_of iova) (iotlb_invalidate iotlb iova).
Proof.
  intros Ha Hr Hv Hl Hn Hne.
  split.
  - apply (amdvi_unmap_faults root mem iova p3 a Ha Hr Hv Hl Hn Hne).
  - apply (iotlb_invalidate_removes iotlb iova).
Qed.

(* ============================================================
   S4.4 conformance oracle: the AMD-Vi 4-level walk agrees with the upstream
   Sv39 oracle, replayed through the level-3 resolution + `translate` re-root.
   ============================================================ *)

(* The AMD-Vi 4-level oracle: level-3 resolves to a valid non-leaf non-NAPOT
   PTE, then the upstream Sv39 oracle re-rooted at that PTE. *)
Definition oracle_amdvi_walk (root : mword 44) (mem : list MemEntry) (iova : mword 64)
  : option (mword 56 * Perm) :=
  match read_pte mem (pte_address root (vpn3 iova)) with
  | None => None
  | Some p3 =>
      if andb p3.(Pte_valid) (andb (negb (is_leaf p3)) (negb p3.(Pte_napot))) then
        oracle_walk p3.(Pte_ppn) mem iova
      else None
  end.

(* The 4-level walk agrees with the upstream oracle exactly: the bottom 3 levels
   are `translate` re-rooted, so G1's `translate_conforms` closes the tail. *)
Theorem amdvi_walk_conforms (root : mword 44) (mem : list MemEntry) (iova : mword 64) :
  amdvi_walk root mem iova = oracle_amdvi_walk root mem iova.
Proof.
  unfold amdvi_walk, oracle_amdvi_walk.
  destruct (read_pte mem (pte_address root (vpn3 iova))) as [p3|] eqn:E; [| reflexivity].
  destruct (andb p3.(Pte_valid) (andb (negb (is_leaf p3)) (negb p3.(Pte_napot)))) eqn:G.
  - rewrite (translate_conforms ({| Core_satp_ppn := p3.(Pte_ppn); Core_tlb := []; Core_hart := 0; Core_node := 0 |}) mem iova).
    cbn [Core_satp_ppn]. reflexivity.
  - reflexivity.
Qed.

(* ============================================================
   S4.5 AMD-Vi walker replay of the fill-on-miss loop: the AMD-Vi translation
   service loop (`amdvi_translate_fill`, machine.sail) consults its IOTLB
   (keyed by (device_id, IOVA); device_id 0 with no SVM) before the 4-level
   walk.  A miss re-walks the 4-level I/O page table and refills the IOTLB;
   after an INVALIDATE_IOMMU_PAGES of the page no cached entry survives, so
   the loop re-walks and recovers — the invalidate-then-retranslate cycle
   (AMD-Vi §2.4.3 / PCIe ATS §4.3, the replay of the VT-d PASID-cache loop
   from S4.5).
   ============================================================ *)

(* A miss re-walks the 4-level I/O page table and refills the IOTLB under
   (0, iova): the loop returns the table result and the refilled cache. *)
Lemma amdvi_translate_fill_miss_refills (root : mword 44) (iotlb : list IotlbEntry)
    (mem : list MemEntry) (iova : mword 64) (pa : mword 56) (perm : Perm) :
  iotlb_lookup iotlb 0 iova = None ->
  amdvi_walk root mem iova = Some (pa, perm) ->
  amdvi_translate_fill root iotlb mem iova
  = (Some (pa, perm),
     {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := iova;
        IotlbEntry_pa := pa; IotlbEntry_perm := perm |} :: iotlb).
Proof.
  intros Hmiss H. unfold amdvi_translate_fill.
  rewrite Hmiss. cbn. rewrite H. cbn. reflexivity.
Qed.

(* After an INVALIDATE_IOMMU_PAGES of the page the cached entry is gone, so
   the loop is forced onto the miss path and recovers by re-walking the
   4-level tables and refilling. *)
Lemma amdvi_translate_fill_after_invalidate (root : mword 44) (iotlb : list IotlbEntry)
    (mem : list MemEntry) (iova : mword 64) (pa : mword 56) (perm : Perm) :
  amdvi_walk root mem iova = Some (pa, perm) ->
  amdvi_translate_fill root (iotlb_invalidate iotlb iova) mem iova
  = (Some (pa, perm),
     {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := iova;
        IotlbEntry_pa := pa; IotlbEntry_perm := perm |} :: iotlb_invalidate iotlb iova).
Proof.
  intros H. unfold amdvi_translate_fill.
  rewrite (iotlb_lookup_after_invalidate iotlb 0 iova). cbn.
  rewrite H. cbn. reflexivity.
Qed.

(* Executable vectors over the S4.4 4-level hit table: the miss -> 4-level
   walk -> refill, and the invalidate-then-retranslate cycle. *)
Definition amdvi_iotlb_hit : IotlbEntry :=
  {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := va0;
     IotlbEntry_pa := expected_pa; IotlbEntry_perm := Read |}.

Lemma test_vector_amdvi_translate_fill_miss :
  amdvi_translate_fill amd_root [] table_amd_hit va0
  = (Some (expected_pa, Read), [amdvi_iotlb_hit]).
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_amdvi_translate_fill_after_invalidate :
  amdvi_translate_fill amd_root (iotlb_invalidate [amdvi_iotlb_hit] va0) table_amd_hit va0
  = (Some (expected_pa, Read), [amdvi_iotlb_hit]).
Proof. vm_compute. reflexivity. Qed.

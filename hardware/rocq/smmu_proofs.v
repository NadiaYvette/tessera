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
Require Import conformance.    (* oracle_walk, translate_conforms *)
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

(* ============================================================
   S4.4 STE/CD structural layer: SID -> STE -> CD -> two-stage walk.

   The stream-table walk (`smmu_translate`) resolves the two roots from the
   stream table (SID-indexed STE) and context-descriptor table (CD).  The
   conformance lemma says a valid STE + CD select exactly `smmu_walk`'s roots
   (the structural layer is a lookup, not a new translation), so every
   coherence/conformance result about `smmu_walk` carries over verbatim.
   ============================================================ *)

(* A valid STE + CD: the stream-table walk is exactly the two-stage walk rooted
   at the CD's stage-1 table and the STE's stage-2 table. *)
Lemma smmu_translate_spec (stes : list Ste) (cds : list Cd) (sid : Z) (mem : list MemEntry)
    (gva : mword 64) (s : Ste) (c : Cd) :
  ste_lookup stes sid = Some s ->
  s.(Ste_valid) = true ->
  cd_lookup cds s.(Ste_cd_ptr) = Some c ->
  c.(Cd_valid) = true ->
  smmu_translate stes cds sid mem gva = smmu_walk c.(Cd_s1_root) s.(Ste_s2_root) mem gva.
Proof.
  intros Hs Hsv Hc Hcv.
  unfold smmu_translate.
  rewrite Hs. cbn. rewrite Hsv. cbn.
  rewrite Hc. cbn. rewrite Hcv. cbn. reflexivity.
Qed.

(* A missing stream-table entry faults. *)
Lemma smmu_translate_faults_missing_ste (stes : list Ste) (cds : list Cd) (sid : Z)
    (mem : list MemEntry) (gva : mword 64) :
  ste_lookup stes sid = None ->
  smmu_translate stes cds sid mem gva = None.
Proof.
  intros Hs. unfold smmu_translate. rewrite Hs. reflexivity.
Qed.

(* An invalid STE faults (no stage-2 root to use). *)
Lemma smmu_translate_faults_invalid_ste (stes : list Ste) (cds : list Cd) (sid : Z)
    (mem : list MemEntry) (gva : mword 64) (s : Ste) :
  ste_lookup stes sid = Some s ->
  s.(Ste_valid) = false ->
  smmu_translate stes cds sid mem gva = None.
Proof.
  intros Hs Hsv. unfold smmu_translate. rewrite Hs. cbn. rewrite Hsv. reflexivity.
Qed.

(* A missing/invalid CD faults (no stage-1 root to use). *)
Lemma smmu_translate_faults_invalid_cd (stes : list Ste) (cds : list Cd) (sid : Z)
    (mem : list MemEntry) (gva : mword 64) (s : Ste) (c : Cd) :
  ste_lookup stes sid = Some s ->
  s.(Ste_valid) = true ->
  cd_lookup cds s.(Ste_cd_ptr) = Some c ->
  c.(Cd_valid) = false ->
  smmu_translate stes cds sid mem gva = None.
Proof.
  intros Hs Hsv Hc Hcv. unfold smmu_translate. rewrite Hs. cbn. rewrite Hsv. cbn.
  rewrite Hc. cbn. rewrite Hcv. reflexivity.
Qed.

(* Test vectors: a missing STE faults; a valid STE+CD resolves to the two-stage
   walk, which faults on the empty table (both stages fault). *)
Lemma test_vector_smmu_translate_empty_stes :
  smmu_translate [] [] 0 [] (mword_of_int 0 : mword 64) = None.
Proof. vm_compute. reflexivity. Qed.

Definition st_ok : Ste :=
  {| Ste_valid := true; Ste_s2_root := mword_of_int 2 : mword 44; Ste_cd_ptr := 0 |}.
Definition cd_ok : Cd :=
  {| Cd_valid := true; Cd_s1_root := mword_of_int 1 : mword 44; Cd_asid := 0 |}.

Lemma test_vector_smmu_translate_hit_empty_walk :
  smmu_translate [st_ok] [cd_ok] 0 [] (mword_of_int 0 : mword 64) = None.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.4 conformance vectors (non-empty): a full two-stage HIT (both stages
   resolve) and the SID -> STE -> CD -> SPA path, pinned against SMMUv3 §3.3
   (stage-1/stage-2 translation) and §3.4 (stream table / context descriptor).
   ============================================================ *)

(* Distinct roots so the stage-1 and stage-2 tables do not alias in the shared
   mem.  Stage-1 maps va0 to GPA 0 (leaf ppn = 0); stage-2 maps va0 (the
   zero-extended GPA) to the SPA [expected_pa]. *)
Definition s1_root : mword 44 := mword_of_int 1.
Definition s1_mid  : mword 44 := mword_of_int 2.
Definition s1_leaf : mword 44 := mword_of_int 3.
Definition s2_root : mword 44 := mword_of_int 4.
Definition s2_mid  : mword 44 := mword_of_int 5.
Definition s2_leaf : mword 44 := mword_of_int 6.

Definition table_s1_gpa0 : PageTable :=
  [ {| MemEntry_addr := pte_address s1_root (vpn2 va0); MemEntry_pte := ptr_pte s1_mid |};
    {| MemEntry_addr := pte_address s1_mid  (vpn1 va0); MemEntry_pte := ptr_pte s1_leaf |};
    {| MemEntry_addr := pte_address s1_leaf (vpn0 va0); MemEntry_pte := ro_pte (mword_of_int 0 : mword 44) |} ].

Definition table_s2_spa : PageTable :=
  [ {| MemEntry_addr := pte_address s2_root (vpn2 va0); MemEntry_pte := ptr_pte s2_mid |};
    {| MemEntry_addr := pte_address s2_mid  (vpn1 va0); MemEntry_pte := ptr_pte s2_leaf |};
    {| MemEntry_addr := pte_address s2_leaf (vpn0 va0); MemEntry_pte := ro_pte leaf_ppn |} ].

Definition mem_smmu_hit : PageTable := List.app table_s1_gpa0 table_s2_spa.

(* Both stages resolve: va0 -> GPA 0 -> SPA [expected_pa] with Read. *)
Lemma test_vector_smmu_two_stage_hit :
  smmu_walk s1_root s2_root mem_smmu_hit va0 = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* The full SID -> STE -> CD -> two-stage walk resolves to the same SPA. *)
Definition st_hit : Ste :=
  {| Ste_valid := true; Ste_s2_root := s2_root; Ste_cd_ptr := 0 |}.
Definition cd_hit : Cd :=
  {| Cd_valid := true; Cd_s1_root := s1_root; Cd_asid := 0 |}.

Lemma test_vector_smmu_translate_hit :
  smmu_translate [st_hit] [cd_hit] 0 mem_smmu_hit va0 = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.4 end-to-end SMMU shootdown (STE/CD threaded through Machine).

   A translation shootdown mutates page tables and caches, never the stream
   table / context-descriptor table — so [smmu_shootdown] unmaps at a root and
   invalidates the IOTLB, threading stes/cds through unchanged.  The end-to-end
   theorem composes the structural lookup ([smmu_translate_spec]) with the
   two-stage coherence replay: after the stage-1 (or stage-2) unmap the full
   SID -> STE -> CD -> two-stage walk faults for the freed frame.
   ============================================================ *)

(* Break-before-make at a page-table root + IOTLB invalidate; the stream table
   and context-descriptor table are carried unchanged. *)
Definition smmu_shootdown (m : Machine) (root : mword 44) (va : mword 64) : Machine :=
  {| Machine_cores := m.(Machine_cores);
     Machine_mem := unmap_leaf_mem (core_with_root root) m.(Machine_mem) va;
     Machine_ram := m.(Machine_ram);
     Machine_ipi := m.(Machine_ipi);
     Machine_iotlb := iotlb_invalidate m.(Machine_iotlb) va;
     Machine_devtlbs := m.(Machine_devtlbs);
     Machine_prireqs := m.(Machine_prireqs);
     Machine_ioqueue := m.(Machine_ioqueue);
     Machine_stes := m.(Machine_stes);
     Machine_cds := m.(Machine_cds) |}.

(* The shootdown's IOTLB is exactly the invalidation of the pre-IOTLB. *)
Lemma smmu_shootdown_iotlb (m : Machine) (root : mword 44) (va : mword 64) :
  (smmu_shootdown m root va).(Machine_iotlb) = iotlb_invalidate m.(Machine_iotlb) va.
Proof. unfold smmu_shootdown. reflexivity. Qed.

(* End-to-end stage-1: unmap the stage-1 leaf, and the full SID -> STE -> CD ->
   two-stage walk faults for the freed frame. *)
Theorem smmu_shootdown_stage1_correct (m : Machine) (sid : Z) (gva : mword 64)
    (s : Ste) (c : Cd) :
  ste_lookup m.(Machine_stes) sid = Some s ->
  s.(Ste_valid) = true ->
  cd_lookup m.(Machine_cds) s.(Ste_cd_ptr) = Some c ->
  c.(Cd_valid) = true ->
  smmu_translate m.(Machine_stes) m.(Machine_cds) sid
    (smmu_shootdown m c.(Cd_s1_root) gva).(Machine_mem) gva = None.
Proof.
  intros Hs Hsv Hc Hcv.
  unfold smmu_shootdown. cbn.
  rewrite (smmu_translate_spec m.(Machine_stes) m.(Machine_cds) sid _ gva s c Hs Hsv Hc Hcv).
  apply (smmu_unmap_stage1_faults c.(Cd_s1_root) s.(Ste_s2_root) m.(Machine_mem) gva).
Qed.

(* End-to-end stage-2: unmap the stage-2 leaf (keyed by the intermediate GPA),
   and — provided stage-1 still resolves to that GPA after the unmap (the
   alias-free premise) — the full walk faults. *)
Theorem smmu_shootdown_stage2_correct (m : Machine) (sid : Z) (gva : mword 64)
    (s : Ste) (c : Cd) (gpa : mword 56) (perm1 : Perm) :
  ste_lookup m.(Machine_stes) sid = Some s ->
  s.(Ste_valid) = true ->
  cd_lookup m.(Machine_cds) s.(Ste_cd_ptr) = Some c ->
  c.(Cd_valid) = true ->
  translate (core_with_root c.(Cd_s1_root))
    (smmu_shootdown m s.(Ste_s2_root) (zero_extend gpa 64)).(Machine_mem) gva = Some (gpa, perm1) ->
  smmu_translate m.(Machine_stes) m.(Machine_cds) sid
    (smmu_shootdown m s.(Ste_s2_root) (zero_extend gpa 64)).(Machine_mem) gva = None.
Proof.
  intros Hs Hsv Hc Hcv H1.
  unfold smmu_shootdown. cbn.
  rewrite (smmu_translate_spec m.(Machine_stes) m.(Machine_cds) sid _ gva s c Hs Hsv Hc Hcv).
  apply (smmu_unmap_stage2_faults c.(Cd_s1_root) s.(Ste_s2_root) m.(Machine_mem) gva gpa perm1 H1).
Qed.

(* ============================================================
   S4.4 conformance oracle: the SMMU walkers agree with the upstream Sv39
   oracle (G1's `translate_conforms`), replayed through the two-stage and the
   stream-table compositions.
   ============================================================ *)

(* The SMMU two-stage oracle: two upstream Sv39 walks composed (GVA -> GPA -> SPA). *)
Definition oracle_smmu_walk (s1_root s2_root : mword 44) (mem : list MemEntry) (gva : mword 64)
  : option (mword 56 * Perm) :=
  match oracle_walk s1_root mem gva with
  | None => None
  | Some (gpa, _) => oracle_walk s2_root mem (zero_extend gpa 64)
  end.

(* The SMMU two-stage walk agrees with the upstream oracle exactly: each stage is
   `translate` re-rooted, so G1's `translate_conforms` transfers stage-by-stage. *)
Theorem smmu_walk_conforms (s1_root s2_root : mword 44) (mem : list MemEntry) (gva : mword 64) :
  smmu_walk s1_root s2_root mem gva = oracle_smmu_walk s1_root s2_root mem gva.
Proof.
  unfold smmu_walk, oracle_smmu_walk.
  rewrite (translate_conforms ({| Core_satp_ppn := s1_root; Core_tlb := []; Core_hart := 0; Core_node := 0 |}) mem gva).
  cbn [Core_satp_ppn].
  destruct (oracle_walk s1_root mem gva) as [[gpa perm1]|] eqn:E.
  - rewrite (translate_conforms ({| Core_satp_ppn := s2_root; Core_tlb := []; Core_hart := 0; Core_node := 0 |}) mem (zero_extend gpa 64)).
    cbn [Core_satp_ppn]. reflexivity.
  - reflexivity.
Qed.

(* The full SID -> STE -> CD -> two-stage walk agrees with the upstream oracle:
   the structural lookup selects the two roots, and `smmu_walk_conforms` closes
   the translation. *)
Theorem smmu_translate_conforms (stes : list Ste) (cds : list Cd) (sid : Z) (mem : list MemEntry)
    (gva : mword 64) (s : Ste) (c : Cd) :
  ste_lookup stes sid = Some s ->
  s.(Ste_valid) = true ->
  cd_lookup cds s.(Ste_cd_ptr) = Some c ->
  c.(Cd_valid) = true ->
  smmu_translate stes cds sid mem gva = oracle_smmu_walk c.(Cd_s1_root) s.(Ste_s2_root) mem gva.
Proof.
  intros Hs Hsv Hc Hcv.
  rewrite (smmu_translate_spec stes cds sid mem gva s c Hs Hsv Hc Hcv).
  apply (smmu_walk_conforms c.(Cd_s1_root) s.(Ste_s2_root) mem gva).
Qed.

(* ============================================================
   S4.5 SMMU walker replay of the fill-on-miss loop: the SMMU's translation
   service loop (`smmu_translate_fill`, machine.sail) consults its IOTLB
   (keyed by (SID, VA) — the ASID is the pasid tag, 0 without SVM) before the
   two-stage walk.  A hit answers from the cache without touching the page
   tables; a miss re-walks STE -> CD -> stage-1/stage-2 and refills the IOTLB
   under (sid, gva); after a 4KiB TLBI of the page no cached entry survives,
   so the loop re-walks and recovers — the invalidate-then-retranslate cycle
   (SMMUv3 §4.4, the replay of the VT-d PASID-cache loop from S4.5).
   ============================================================ *)

(* A hit answers from the cache: the loop returns the cached translation and
   leaves the IOTLB untouched — no table walk is performed. *)
Lemma smmu_translate_fill_hit (stes : list Ste) (cds : list Cd) (sid : Z)
    (iotlb : list IotlbEntry) (mem : list MemEntry) (gva : mword 64)
    (pa : mword 56) (perm : Perm) :
  iotlb_lookup iotlb sid gva = Some (pa, perm) ->
  smmu_translate_fill stes cds sid iotlb mem gva = (Some (pa, perm), iotlb).
Proof.
  intros H. unfold smmu_translate_fill. rewrite H. reflexivity.
Qed.

(* A miss re-walks the two-stage tables and refills the IOTLB under (sid, gva):
   the loop returns the table result and the refilled cache. *)
Lemma smmu_translate_fill_miss_refills (stes : list Ste) (cds : list Cd) (sid : Z)
    (iotlb : list IotlbEntry) (mem : list MemEntry) (gva : mword 64)
    (pa : mword 56) (perm : Perm) :
  iotlb_lookup iotlb sid gva = None ->
  smmu_translate stes cds sid mem gva = Some (pa, perm) ->
  smmu_translate_fill stes cds sid iotlb mem gva
  = (Some (pa, perm),
     {| IotlbEntry_did := sid; IotlbEntry_pasid := 0; IotlbEntry_iova := gva;
        IotlbEntry_pa := pa; IotlbEntry_perm := perm |} :: iotlb).
Proof.
  intros Hmiss H. unfold smmu_translate_fill.
  rewrite Hmiss. cbn. rewrite H. cbn. reflexivity.
Qed.

(* After a 4KiB TLBI of the page the cached entry is gone, so the loop is
   forced onto the miss path and recovers by re-walking the tables and
   refilling — the invalidate-then-retranslate cycle. *)
Lemma smmu_translate_fill_after_invalidate (stes : list Ste) (cds : list Cd) (sid : Z)
    (iotlb : list IotlbEntry) (mem : list MemEntry) (gva : mword 64)
    (pa : mword 56) (perm : Perm) :
  smmu_translate stes cds sid mem gva = Some (pa, perm) ->
  smmu_translate_fill stes cds sid (iotlb_invalidate iotlb gva) mem gva
  = (Some (pa, perm),
     {| IotlbEntry_did := sid; IotlbEntry_pasid := 0; IotlbEntry_iova := gva;
        IotlbEntry_pa := pa; IotlbEntry_perm := perm |} :: iotlb_invalidate iotlb gva).
Proof.
  intros H. unfold smmu_translate_fill.
  rewrite (iotlb_lookup_after_invalidate iotlb sid gva). cbn.
  rewrite H. cbn. reflexivity.
Qed.

(* Executable vectors over the S4.4 two-stage hit table: the cached hit, the
   miss -> table walk -> refill, and the invalidate-then-retranslate cycle
   (the invalidation drops the cached entry; the loop re-walks and refills it
   back). *)
Definition smmu_iotlb_hit : IotlbEntry :=
  {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := va0;
     IotlbEntry_pa := expected_pa; IotlbEntry_perm := Read |}.

Lemma test_vector_smmu_translate_fill_hit :
  smmu_translate_fill [st_hit] [cd_hit] 0 [smmu_iotlb_hit] mem_smmu_hit va0
  = (Some (expected_pa, Read), [smmu_iotlb_hit]).
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_smmu_translate_fill_miss :
  smmu_translate_fill [st_hit] [cd_hit] 0 [] mem_smmu_hit va0
  = (Some (expected_pa, Read),
     [{| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := va0;
        IotlbEntry_pa := expected_pa; IotlbEntry_perm := Read |}]).
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_smmu_translate_fill_after_invalidate :
  smmu_translate_fill [st_hit] [cd_hit] 0 (iotlb_invalidate [smmu_iotlb_hit] va0) mem_smmu_hit va0
  = (Some (expected_pa, Read), [smmu_iotlb_hit]).
Proof. vm_compute. reflexivity. Qed.

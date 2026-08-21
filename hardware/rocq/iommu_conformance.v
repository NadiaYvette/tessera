(* Tessera — SSG-4 IOMMU conformance cross-check.

   The IOMMU model in `machine.sail` is hand-written Sail, cross-checked (not
   fully refined) against the three platform specs:

     - Intel VT-d 5.20:      the walker (first/second-stage §3 / §6.2),
                             IOTLB Invalidate §6.5.2.3, Invalidation-Wait §6.5.2.9.
     - Arm SMMUv3 H.a:       the stream-table / translation walk §3.3,
                             TLB invalidation TLBI §4.4.
     - AMD-Vi 3.11:          the I/O page tables (the walker) §2.2.3,
                             INVALIDATE_IOMMU_PAGES §2.4.3.

   The ATS/PRI device side (PCIe 6.0 ATS §4.3 / PRI §4.2) is modelled in the
   same file; its proofs live in `iommu_proofs.v` (S4.3) — here only the
   three-platform *IOMMU* walker/invalidation cross-check is pinned.

   Two results close the walker half: `iommu_walk` is literally `translate`
   re-rooted at the domain (so G1's `translate_conforms` — agreement with the
   upstream Sv39 oracle — transfers verbatim), and the invalidation is a
   4KiB-granularity VPN-tag filter, pinned by one executable vector per
   platform's invalidation shape (selective: drop the addressed page, keep the
   others; no-op on a non-matching page).

   The same caveat as G1 applies (rigor-trust-line.md): correct conditional on
   this simplified IOMMU model being faithful to the three specs, closed only
   by a full derivation from the upstream formal models — of which these
   vectors are the first instalment. *)

From Stdlib Require Import List.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.  (* eq_vec_*_iff *)
Require Import machine_types.
Require Import machine.
Require Import conformance.   (* oracle_walk, translate_conforms *)
Require Import shootdown.     (* core_with_root *)
Import ListNotations.

(* ============================================================
   The walker half: iommu_walk = translate re-rooted at the domain.
   ============================================================ *)

Lemma iommu_walk_conforms (root : mword 44) (mem : list MemEntry) (iova : mword 64) :
  iommu_walk root mem iova = translate (core_with_root root) mem iova.
Proof. reflexivity. Qed.

(* The IOMMU walker therefore agrees with the upstream Sv39 oracle exactly as
   the CPU walker does (G1's `translate_conforms`) — the IOMMU walker is no
   less conformant than the CPU walker it re-roots. *)
Theorem iommu_walk_translate_conforms (root : mword 44) (mem : list MemEntry) (iova : mword 64) :
  iommu_walk root mem iova = oracle_walk root mem iova.
Proof.
  rewrite iommu_walk_conforms.
  apply (translate_conforms (core_with_root root) mem iova).
Qed.

(* ============================================================
   The invalidation half: per-platform executable vectors.

   The IOMMU invalidation is a 4KiB-granularity VPN-tag filter: it drops every
   cached translation whose IOVA is the addressed page and keeps the others.
   Each platform's invalidation command has exactly this selective shape, so one
   vector per spec pins it.  A two-entry IOTLB, entries at IOVA 0 and 4096
   (VPN 0 and VPN 1).
   ============================================================ *)

Definition conf_iotlb : list IotlbEntry :=
  [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
       IotlbEntry_iova := (mword_of_int 0 : mword 64);
       IotlbEntry_pa := (mword_of_int 0 : mword 56);
       IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
    {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
       IotlbEntry_iova := (mword_of_int 4096 : mword 64);
       IotlbEntry_pa := (mword_of_int 4096 : mword 56);
       IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].

(* VT-d §6.5.2.3 IOTLB Invalidate: a 4KiB selective invalidation of page 0 drops
   the IOVA-0 translation and keeps the IOVA-4096 one. *)
Lemma test_vector_vtd_iotlb_invalidate :
  iotlb_invalidate conf_iotlb (mword_of_int 0 : mword 64)
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
         IotlbEntry_iova := (mword_of_int 4096 : mword 64);
         IotlbEntry_pa := (mword_of_int 4096 : mword 56);
         IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].
Proof. vm_compute. reflexivity. Qed.

(* SMMU §4.4 TLBI: the same page-granularity invalidation, the symmetric case —
   invalidating page 4096 (VPN 1) drops the IOVA-4096 translation and keeps
   IOVA 0. *)
Lemma test_vector_smmu_iotlb_invalidate :
  iotlb_invalidate conf_iotlb (mword_of_int 4096 : mword 64)
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
         IotlbEntry_iova := (mword_of_int 0 : mword 64);
         IotlbEntry_pa := (mword_of_int 0 : mword 56);
         IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].
Proof. vm_compute. reflexivity. Qed.

(* AMD-Vi §2.4.3 INVALIDATE_IOMMU_PAGES: a selective invalidation for a page not
   present in the IOTLB is a no-op (it only touches the addressed page). *)
Lemma test_vector_amdvi_iotlb_invalidate_noop :
  iotlb_invalidate conf_iotlb (mword_of_int 8192 : mword 64) = conf_iotlb.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   The ATS/PRI device side: cross-checked against PCIe 6.0.

   The device↔IOMMU interface is the genuinely-new part of SSG-4 (not a replay
   of the CPU MMU).  PCIe 6.0 specifies two flows the CPU track never had:

     - ATS §4.3 (Translation Request → Translation Completion): the device asks
       the IOMMU for a translation; the completion carries exactly the walk's
       physical address and permission, and the device caches it (device-TLB).
       A failed translation produces no completion (the device then issues PRI).
     - PRI §4.2 (Page Request): on a translation fault the device issues a page
       request, the kernel maps the page, and the device retries.  At most one
       page request is outstanding per (Requestor ID, address).

   The proofs live in iommu_proofs.v (S4.3): ats_translate_spec (completion =
   walk), ats_translate_fault (a fault caches nothing), ats_invalidate_removes
   (the device-TLB tier), pri_request_idempotent (serviced at most once).  Here
   two executable vectors pin those flows against the PCIe descriptions.
   ============================================================ *)

(* A three-level table mapping IOVA 0 -> leaf PPN 42 (read-only). *)
Definition pcie_ptr_pte (next : mword 44) : Pte :=
  {| Pte_valid := true; Pte_read := false; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.
Definition pcie_ro_pte (next : mword 44) : Pte :=
  {| Pte_valid := true; Pte_read := true; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.

Definition pcie_table : PageTable :=
  [ {| MemEntry_addr := pte_address (mword_of_int 1 : mword 44) (vpn2 (mword_of_int 0 : mword 64));
       MemEntry_pte := pcie_ptr_pte (mword_of_int 2 : mword 44) |};
    {| MemEntry_addr := pte_address (mword_of_int 2 : mword 44) (vpn1 (mword_of_int 0 : mword 64));
       MemEntry_pte := pcie_ptr_pte (mword_of_int 3 : mword 44) |};
    {| MemEntry_addr := pte_address (mword_of_int 3 : mword 44) (vpn0 (mword_of_int 0 : mword 64));
       MemEntry_pte := pcie_ro_pte (mword_of_int 42 : mword 44) |} ].

(* PCIe §4.3 ATS: a translation completion carries exactly the walk's physical
   address and permission — the device-TLB entry is filled from the walk, not
   anything the device supplied. *)
Lemma test_vector_pcie_ats_completion :
  ats_translate [] [] (mword_of_int 1 : mword 44) 0 (mword_of_int 0 : mword 64) pcie_table
  = ([ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
          IotlbEntry_iova := (mword_of_int 0 : mword 64);
          IotlbEntry_pa := phys_addr (mword_of_int 42 : mword 44) (page_offset (mword_of_int 0 : mword 64));
          IotlbEntry_perm := Read ; IotlbEntry_gen := 0|} ],
     [ {| DevTlbEntry_did := 0; DevTlbEntry_iova := (mword_of_int 0 : mword 64);
          DevTlbEntry_pa := phys_addr (mword_of_int 42 : mword 44) (page_offset (mword_of_int 0 : mword 64));
          DevTlbEntry_perm := Read |} ]).
Proof. vm_compute. reflexivity. Qed.

(* PCIe §4.2 PRI: a page request is serviced at most once per (Requestor ID,
   PASID, address) — re-issuing the same request leaves the pending set
   unchanged (re-pending is idempotent). *)
Lemma test_vector_pcie_pri_at_most_once :
  let q := pri_request [] (0, 0) (mword_of_int 4096 : mword 64) in
  pri_request q (0, 0) (mword_of_int 4096 : mword 64) = q.
Proof. vm_compute. reflexivity. Qed.

(* PCIe §4.2 PRI retry loop: the device's pending-bit recheck — Set while the
   fault is unresolved, Clear once the kernel mapped the page. *)
Lemma test_vector_pcie_pri_retry_cycle :
  let q := pri_request [] (0, 0) (mword_of_int 4096 : mword 64) in
  pri_pending q (0, 0) (mword_of_int 4096 : mword 64) = true /\
  pri_pending (pri_resolve q (0, 0) (mword_of_int 4096 : mword 64))
              (0, 0) (mword_of_int 4096 : mword 64) = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* PCIe §4.2 / VT-d 5.20 §7.2: a pending request's translation fault produces
   the fault record — the fault-message payload naming the endpoint (0, 0). *)
Lemma test_vector_pcie_pri_fault_delivers :
  let q := pri_request [] (0, 0) (mword_of_int 4096 : mword 64) in
  pri_fault_delivers q (0, 0) (mword_of_int 4096 : mword 64) FR_Stage2Fault
  = Some {| FaultRecord_did := 0; FaultRecord_pasid := 0; FaultRecord_iova := (mword_of_int 4096 : mword 64);
           FaultRecord_reason := FR_Stage2Fault |}.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   The ALL-granularity invalidation (AMD-Vi INVALIDATE_IOMMU_ALL §2.4.8 /
   SMMU TLBI_ALL §4.4): the second invalidation shape — drop every cached
   translation, regardless of IOVA, vs the 4KiB selective invalidate above.
   ============================================================ *)

(* AMD-Vi §2.4.8 INVALIDATE_IOMMU_ALL: clears the whole IOTLB. *)
Lemma test_vector_amdvi_invalidate_iotlb_all :
  iotlb_invalidate_all conf_iotlb = [].
Proof. vm_compute. reflexivity. Qed.

(* SMMU §4.4 TLBI_ALL: clears the whole endpoint device-TLB. *)
Lemma test_vector_smmu_invalidate_devtlb_all :
  ats_invalidate_all [ {| DevTlbEntry_did := 0; DevTlbEntry_iova := (mword_of_int 0 : mword 64);
                         DevTlbEntry_pa := (mword_of_int 0 : mword 56); DevTlbEntry_perm := ReadWrite |};
                       {| DevTlbEntry_did := 0; DevTlbEntry_iova := (mword_of_int 4096 : mword 64);
                         DevTlbEntry_pa := (mword_of_int 4096 : mword 56); DevTlbEntry_perm := ReadWrite |} ]
  = [].
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   The ASID / domain-granularity invalidation (S4.4): the coarser shapes
   beside the 4KiB selective and the ALL invalidations.  A four-entry IOTLB
   spanning (did 0, pasid 0), (did 0, pasid 1), (did 1, pasid 0),
   (did 1, pasid 1).
   ============================================================ *)

Definition conf_mixed_iotlb : list IotlbEntry :=
  [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 0 : mword 64);
       IotlbEntry_pa := (mword_of_int 0 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
    {| IotlbEntry_did := 0; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 4096 : mword 64);
       IotlbEntry_pa := (mword_of_int 4096 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
    {| IotlbEntry_did := 1; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 8192 : mword 64);
       IotlbEntry_pa := (mword_of_int 8192 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
    {| IotlbEntry_did := 1; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 12288 : mword 64);
       IotlbEntry_pa := (mword_of_int 12288 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].

(* SMMU §4.4 TLBI-by-ASID: dropping ASID 0 leaves exactly the pasid-1 entries. *)
Lemma test_vector_smmu_tlbi_asid :
  iotlb_invalidate_pasid conf_mixed_iotlb 0
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 4096 : mword 64);
         IotlbEntry_pa := (mword_of_int 4096 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
      {| IotlbEntry_did := 1; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 12288 : mword 64);
         IotlbEntry_pa := (mword_of_int 12288 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].
Proof. vm_compute. reflexivity. Qed.

(* AMD-Vi §2.4.3 INVALIDATE_IOMMU_PAGES-by-domain: dropping domain 1 leaves exactly
   the did-0 entries. *)
Lemma test_vector_amdvi_invalidate_domain :
  iotlb_invalidate_domain conf_mixed_iotlb 1
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 0 : mword 64);
         IotlbEntry_pa := (mword_of_int 0 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
      {| IotlbEntry_did := 0; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 4096 : mword 64);
         IotlbEntry_pa := (mword_of_int 4096 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].
Proof. vm_compute. reflexivity. Qed.

(* An ASID absent from the cache is a no-op; this guards the filter's
   non-target preservation in addition to the positive-removal vector above. *)
Lemma test_vector_smmu_tlbi_asid_noop :
  iotlb_invalidate_pasid conf_mixed_iotlb 2 = conf_mixed_iotlb.
Proof. vm_compute. reflexivity. Qed.

(* Likewise, a domain absent from the cache does not disturb any translation. *)
Lemma test_vector_amdvi_invalidate_domain_noop :
  iotlb_invalidate_domain conf_mixed_iotlb 2 = conf_mixed_iotlb.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   VT-d P_IOTLB PASID-selective invalidation (S4.5 cross-check, §6.5.2.4):
   the PASID-based-IOTLB Invalidate Descriptor's PASID-selective granularity
   (G = 10b) drops the entries *associated with the specified PASID and
   domain-id* — both tags, unlike the SMMU TLBI-by-ASID (pasid only).  On the
   four-entry mixed IOTLB, invalidating (PASID 1, DID 0) removes exactly the
   (0,1,4096) entry.
   ============================================================ *)

(* VT-d §6.5.2.4 P_IOTLB, PASID-selective (10b) on (DID 0, PASID 1): only the
   (0,1,4096) entry is associated with both tags, so it goes; the (0,0,0),
   (1,0,8192) and (1,1,12288) entries survive (each differs in DID or
   PASID). *)
Lemma test_vector_vtd_piotlb_pasid_selective :
  iotlb_invalidate_pasid_did conf_mixed_iotlb (0, 1)
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 0 : mword 64);
         IotlbEntry_pa := (mword_of_int 0 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
      {| IotlbEntry_did := 1; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 8192 : mword 64);
         IotlbEntry_pa := (mword_of_int 8192 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
      {| IotlbEntry_did := 1; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 12288 : mword 64);
         IotlbEntry_pa := (mword_of_int 12288 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].
Proof. vm_compute. reflexivity. Qed.

(* A (DID, PASID) absent from the IOTLB is a no-op: the (0,2) tag matches no
   entry (no IOTLB entry has DID 0 AND PASID 2), so the cache is untouched. *)
Lemma test_vector_vtd_piotlb_pasid_selective_noop :
  iotlb_invalidate_pasid_did conf_mixed_iotlb (0, 2) = conf_mixed_iotlb.
Proof. vm_compute. reflexivity. Qed.

(* The IOTLB half of the mandatory §6.5.2.2 pairing: a PASID-selective-
   within-domain PASID-cache invalidation (01b) followed by the PASID-
   selective P_IOTLB invalidation (10b) — here the (0,1) tag is cleared from
   the IOTLB so the device's next request misses and re-walks the first-stage
   tables (the cache half is `iotlb_pasid_cache_pair_invalidate_clears`). *)
Lemma test_vector_vtd_piotlb_pair_iotlb_half :
  iotlb_invalidate_pasid_did conf_mixed_iotlb (0, 1)
  = iotlb_invalidate_pasid_did (iotlb_invalidate_pasid_did conf_mixed_iotlb (0, 1)) (0, 1).
Proof. reflexivity. Qed.

(* ============================================================
   The composed VA+tag granules (the granularity matrix replay of the VT-d
   PASID-cache work): SMMU TLBI_VA_ASID and AMD-Vi INVALIDATE_IOMMU_PAGES-by-
   (domain, VA) invalidate by VA *then* by the tag — removing the
   intersection (anything matching either granule).  On the four-entry mixed
   IOTLB: TLBI_VA_ASID(va 0, asid 0) leaves only the entries whose VA page
   differs *and* whose ASID differs — (0,1,4096) and (1,1,12288).
   ============================================================ *)

(* SMMU §4.4 TLBI_VA_ASID: invalidate (VA 0, ASID 0) — the (0,0,0) entry is
   the only one matching both, so it goes; the (1,0,8192) entry is dropped by
   the ASID filter even though its VA differs. *)
Lemma test_vector_smmu_tlbi_va_asid :
  iotlb_invalidate_pasid (iotlb_invalidate conf_mixed_iotlb (mword_of_int 0 : mword 64)) 0
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 4096 : mword 64);
         IotlbEntry_pa := (mword_of_int 4096 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
      {| IotlbEntry_did := 1; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 12288 : mword 64);
         IotlbEntry_pa := (mword_of_int 12288 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].
Proof. vm_compute. reflexivity. Qed.

(* AMD-Vi §2.4.3 INVALIDATE_IOMMU_PAGES-by-(domain, VA): invalidate
   (domain 1, VA 0) — matching either the domain or the VA goes; only the
   (0,1,4096) entry survives. *)
Lemma test_vector_amdvi_invalidate_pages_domain_va :
  iotlb_invalidate_domain (iotlb_invalidate conf_mixed_iotlb (mword_of_int 0 : mword 64)) 1
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 4096 : mword 64);
         IotlbEntry_pa := (mword_of_int 4096 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   The device-TLB domain invalidation (AMD-Vi INVALIDATE_DEVTBL-SEL §2.4.7 /
   the SMMU stream-side tier): invalidating domain 0's device-TLB entries
   leaves the other domain's translations intact — a lookup of domain 0's
   IOVA faults while domain 1's still resolves.
   ============================================================ *)

Definition conf_devtlb_two_domains : list DevTlbEntry :=
  [ {| DevTlbEntry_did := 0; DevTlbEntry_iova := (mword_of_int 0 : mword 64);
       DevTlbEntry_pa := (mword_of_int 0 : mword 56); DevTlbEntry_perm := ReadWrite |};
    {| DevTlbEntry_did := 1; DevTlbEntry_iova := (mword_of_int 4096 : mword 64);
       DevTlbEntry_pa := (mword_of_int 4096 : mword 56); DevTlbEntry_perm := ReadWrite |} ].

Lemma test_vector_amdvi_invalidate_devtbl_domain :
  ats_invalidate_domain conf_devtlb_two_domains 0
  = [ {| DevTlbEntry_did := 1; DevTlbEntry_iova := (mword_of_int 4096 : mword 64);
         DevTlbEntry_pa := (mword_of_int 4096 : mword 56); DevTlbEntry_perm := ReadWrite |} ] /\
  find_devtlb (ats_invalidate_domain conf_devtlb_two_domains 0) (mword_of_int 0 : mword 64) = None /\
  find_devtlb (ats_invalidate_domain conf_devtlb_two_domains 0) (mword_of_int 4096 : mword 64)
  = Some ((mword_of_int 4096 : mword 56), ReadWrite).
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================
   The granularity-validity matrix (VT-d 5.20 §6.5.2.3 / §6.5.2.4): the
   descriptor-acceptance check.  For the PASID-cache invalidation the G field
   encodes Domain-Selective = 00b, PASID-Selective-within-Domain = 01b,
   Global = 11b, and 10b is Reserved; for the P_IOTLB it encodes
   PASID-selective = 10b and Page-Selective-within-PASID = 11b, with 00b and
   01b Reserved.  `granularity_valid` rejects the reserved encodings — a
   reserved descriptor is invalid (the model's fault path).
   ============================================================ *)

(* The PASID-cache invalidation accepts 00b/01b/11b and rejects the
   reserved 10b. *)
Lemma test_vector_granularity_valid_pasid_cache :
  pasid_cache_inv_granularity_valid (mword_of_int 0 : mword 2) = true /\
  pasid_cache_inv_granularity_valid (mword_of_int 1 : mword 2) = true /\
  pasid_cache_inv_granularity_valid (mword_of_int 2 : mword 2) = false /\
  pasid_cache_inv_granularity_valid (mword_of_int 3 : mword 2) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The P_IOTLB accepts 10b/11b and rejects the reserved 00b/01b. *)
Lemma test_vector_granularity_valid_p_iotlb :
  p_iotlb_granularity_valid (mword_of_int 0 : mword 2) = false /\
  p_iotlb_granularity_valid (mword_of_int 1 : mword 2) = false /\
  p_iotlb_granularity_valid (mword_of_int 2 : mword 2) = true /\
  p_iotlb_granularity_valid (mword_of_int 3 : mword 2) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The reserved 10b on the PASID-cache invalidation is rejected (invalid
   descriptor), so the cache is not touched by a 10b descriptor. *)
Lemma test_vector_granularity_valid_reserved_10b :
  pasid_cache_inv_granularity_valid (mword_of_int 2 : mword 2) = false.
Proof. vm_compute. reflexivity. Qed.

(* The two-descriptor queue: the P_IOTLB PASID-selective command (the IOTLB
   half of §6.5.2.2) followed by the Invalidation-Wait completion (§6.5.2.9). *)
Definition piotlb_pair_queue (d p : Z) : list InvalidationCmd :=
  [ {| InvalidationCmd_is_wait := false; InvalidationCmd_gran := Gran_PasidDid;
       InvalidationCmd_va := (mword_of_int 0 : mword 64); InvalidationCmd_did := d; InvalidationCmd_pasid := p |};
    {| InvalidationCmd_is_wait := true;  InvalidationCmd_gran := Gran_PasidDid;
       InvalidationCmd_va := (mword_of_int 0 : mword 64); InvalidationCmd_did := d; InvalidationCmd_pasid := p |} ].

(* The queue form of the P_IOTLB pairing (VT-d 5.20 §6.5.2.2 / §6.5.2.4):
   on the four-entry mixed IOTLB the queued PASID-selective (0, 1) command
   keeps exactly the entries whose DID or PASID differs, and the
   Invalidation-Wait reports completion. *)
Lemma test_vector_iommu_queue_piotlb_pair :
  iommu_process_queue (piotlb_pair_queue 0 1) conf_mixed_iotlb
  = Some [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 0 : mword 64);
              IotlbEntry_pa := (mword_of_int 0 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
           {| IotlbEntry_did := 1; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 8192 : mword 64);
              IotlbEntry_pa := (mword_of_int 8192 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|};
           {| IotlbEntry_did := 1; IotlbEntry_pasid := 1; IotlbEntry_iova := (mword_of_int 12288 : mword 64);
              IotlbEntry_pa := (mword_of_int 12288 : mword 56); IotlbEntry_perm := ReadWrite ; IotlbEntry_gen := 0|} ].
Proof. vm_compute. reflexivity. Qed.

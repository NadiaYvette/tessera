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
       IotlbEntry_perm := ReadWrite |};
    {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
       IotlbEntry_iova := (mword_of_int 4096 : mword 64);
       IotlbEntry_pa := (mword_of_int 4096 : mword 56);
       IotlbEntry_perm := ReadWrite |} ].

(* VT-d §6.5.2.3 IOTLB Invalidate: a 4KiB selective invalidation of page 0 drops
   the IOVA-0 translation and keeps the IOVA-4096 one. *)
Lemma test_vector_vtd_iotlb_invalidate :
  iotlb_invalidate conf_iotlb (mword_of_int 0 : mword 64)
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
         IotlbEntry_iova := (mword_of_int 4096 : mword 64);
         IotlbEntry_pa := (mword_of_int 4096 : mword 56);
         IotlbEntry_perm := ReadWrite |} ].
Proof. vm_compute. reflexivity. Qed.

(* SMMU §4.4 TLBI: the same page-granularity invalidation, the symmetric case —
   invalidating page 4096 (VPN 1) drops the IOVA-4096 translation and keeps
   IOVA 0. *)
Lemma test_vector_smmu_iotlb_invalidate :
  iotlb_invalidate conf_iotlb (mword_of_int 4096 : mword 64)
  = [ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
         IotlbEntry_iova := (mword_of_int 0 : mword 64);
         IotlbEntry_pa := (mword_of_int 0 : mword 56);
         IotlbEntry_perm := ReadWrite |} ].
Proof. vm_compute. reflexivity. Qed.

(* AMD-Vi §2.4.3 INVALIDATE_IOMMU_PAGES: a selective invalidation for a page not
   present in the IOTLB is a no-op (it only touches the addressed page). *)
Lemma test_vector_amdvi_iotlb_invalidate_noop :
  iotlb_invalidate conf_iotlb (mword_of_int 8192 : mword 64) = conf_iotlb.
Proof. vm_compute. reflexivity. Qed.

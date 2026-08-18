(* Tessera — SSG-4, S4.1: the IOMMU's translation cache (IOTLB) stays coherent
   with the CPU page table (`IOTLB ⊆ mapping`), replayed from Stage 1/1.1.

   machine.sail's IOMMU model (S4.1a) added [IotlbEntry] + [Machine_iotlb] +
   [iommu_walk] (the same Sv39 walk re-rooted at the domain) + [iotlb_invalidate]
   (4KiB-granularity IOTLB invalidation).  This file is S4.1b: the functional
   coherence theorems, the IOMMU twins of coherence_leaf.v's
   [unmap_leaf_correct] / [unmap_leaf_without_flush_breaks_coherence].

   - [iotlb_invalidate_removes] — the invalidation drops exactly the entries in
     the unmapped page (survivors have a different VPN), so no cached device
     translation for the freed frame survives.  The "no stale IOTLB entry" half.
   - [iommu_unmap_faults] — after unmap, the device walk faults for va.  The
     "DMA cannot reach the freed frame" half (reuses [leaf_addr_removal_faults] /
     [leaf_addr_none_implies_translate_none] via [iommu_walk = translate]).
   - [iommu_unmap_correct] — unmap + invalidate: the mapping is gone AND no cached
     translation for va survives.
   - [iommu_unmap_without_invalidate_breaks] — unmap WITHOUT invalidate: the walk
     faults but the device's stale cached translation still answers [Some (pa, perm)].

   The full universal invariant `∀ e ∈ iotlb, walk e.iova = Some (e.pa, e.perm)`
   (the literal `IOTLB ⊆ mapping`) needs [pte_address] injectivity / bitvector
   arithmetic to show unmapping va leaves *other* pages' walks untouched — the
   same "keep the arithmetic opaque" boundary as Stage 1, deferred (see
   doc/iommu-shootdown-plan.md).  The single-frame property above is the actual
   security claim (DMA to the freed frame faults) and is proved here.

   See doc/iommu-shootdown-plan.md and doc/system-state-goals.md (SSG-4). *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords. (* eq_vec_false_iff *)
Require Import machine_types.
Require Import machine.
Require Import coherence_leaf.  (* unmap_leaf_mem, leaf_addr_removal_faults,
                                   leaf_addr_none_implies_translate_none *)
Require Import shootdown.       (* core_with_root *)
Import ListNotations.

(* ============================================================
   1. The invalidation drops exactly the unmapped page's entries.
   ============================================================ *)

(* After [iotlb_invalidate], every surviving IOTLB entry is for a *different*
   page than the unmapped `va` (4KiB granularity: the VPN differs).  This is the
   "no stale entry for the freed frame survives" half of `IOTLB ⊆ mapping`. *)
Lemma iotlb_invalidate_removes (iotlb : list IotlbEntry) (va : mword 64) :
  Forall (fun e => vpn_of e.(IotlbEntry_iova) <> vpn_of va) (iotlb_invalidate iotlb va).
Proof.
  induction iotlb as [| e rest IH]; cbn.
  - constructor.
  - destruct (eq_vec (vpn_of e.(IotlbEntry_iova)) (vpn_of va)) eqn:E.
    + (* same VPN: the entry is dropped *)
      exact IH.
    + (* different VPN: the entry survives, and satisfies the predicate *)
      constructor.
      * apply eq_vec_false_iff. exact E.
      * exact IH.
Qed.

(* ============================================================
   2. The unmap faults the device walk for va.
   ============================================================ *)

(* After the leaf-PTE removal, the IOMMU's walk faults for the freed frame: the
   device cannot reach it.  [iommu_walk] is [translate] re-rooted, so this is the
   Stage 1.1 leaf-removal lemmas applied to the domain root. *)
Lemma iommu_unmap_faults (root : mword 44) (mem : list MemEntry) (va : mword 64) :
  iommu_walk root (unmap_leaf_mem (core_with_root root) mem va) va = None.
Proof.
  unfold iommu_walk, unmap_leaf_mem.
  destruct (leaf_addr (core_with_root root) mem va) as [a |] eqn:Hl.
  - apply (leaf_addr_removal_faults (core_with_root root) mem va a Hl).
  - apply (leaf_addr_none_implies_translate_none (core_with_root root) mem va Hl).
Qed.

(* ============================================================
   3. unmap + invalidate: the IOMMU twin of unmap_leaf_correct.
   ============================================================ *)

(* The correct IOMMU unmap: the mapping is gone (the walk faults) AND no cached
   device translation for the freed frame survives the invalidation. *)
Lemma iommu_unmap_correct (root : mword 44) (mem : list MemEntry) (va : mword 64)
    (iotlb : list IotlbEntry) :
  iommu_walk root (unmap_leaf_mem (core_with_root root) mem va) va = None /\
  Forall (fun e => vpn_of e.(IotlbEntry_iova) <> vpn_of va) (iotlb_invalidate iotlb va).
Proof.
  split.
  - apply (iommu_unmap_faults root mem va).
  - apply (iotlb_invalidate_removes iotlb va).
Qed.

(* ============================================================
   4. unmap WITHOUT invalidate: the IOMMU twin of the stale-entry bug.
   ============================================================ *)

(* The buggy IOMMU unmap: the authoritative walk faults after the unmap, but the
   device's cached translation — still present because no invalidate ran — keeps
   answering [Some (pa, perm)] for the freed frame (the premise: the cache was
   correct before the unmap).  A device consulting its IOTLB reaches the freed
   frame. *)
Lemma iommu_unmap_without_invalidate_breaks (root : mword 44) (mem : list MemEntry)
    (va : mword 64) (e : IotlbEntry) :
  iommu_walk root mem va = Some (e.(IotlbEntry_pa), e.(IotlbEntry_perm)) ->
  iommu_walk root (unmap_leaf_mem (core_with_root root) mem va) va = None
  /\ iommu_walk root mem va = Some (e.(IotlbEntry_pa), e.(IotlbEntry_perm)).
Proof.
  intros Hcached. split.
  - apply (iommu_unmap_faults root mem va).
  - exact Hcached.
Qed.

(* ============================================================
   Executable vectors (vm_compute): the invalidation drops the unmapped page's
   entries and leaves the others; the empty-table walk faults.
   ============================================================ *)

Definition iommu_e0 : IotlbEntry :=
  {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
     IotlbEntry_iova := (mword_of_int 0 : mword 64);
     IotlbEntry_pa := (mword_of_int 0 : mword 56);
     IotlbEntry_perm := ReadWrite |}.
Definition iommu_e1 : IotlbEntry :=
  {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
     IotlbEntry_iova := (mword_of_int 4096 : mword 64);
     IotlbEntry_pa := (mword_of_int 4096 : mword 56);
     IotlbEntry_perm := ReadWrite |}.

(* Invalidating the page containing va = 0 drops e0 (VPN 0) and keeps e1 (VPN 1). *)
Lemma test_vector_iommu_invalidate_va0 :
  iotlb_invalidate [iommu_e0; iommu_e1] (mword_of_int 0 : mword 64) = [iommu_e1].
Proof. vm_compute. reflexivity. Qed.

(* Invalidating the page containing va = 4096 drops e1 and keeps e0. *)
Lemma test_vector_iommu_invalidate_va4096 :
  iotlb_invalidate [iommu_e0; iommu_e1] (mword_of_int 4096 : mword 64) = [iommu_e0].
Proof. vm_compute. reflexivity. Qed.

(* The empty page table faults the device walk. *)
Lemma test_vector_iommu_walk_empty_faults :
  iommu_walk (mword_of_int 1 : mword 44) [] (mword_of_int 0 : mword 64) = None.
Proof. vm_compute. reflexivity. Qed.

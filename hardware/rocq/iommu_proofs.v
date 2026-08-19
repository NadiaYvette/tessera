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
Require Import SailStdpp.MachineWord.  (* slice / word_to_N (unfolding subrange_vec_dec) *)
Require Import machine_types.
Require Import machine.
Require Import coherence.       (* remove_entry, read_pte_absent_after_remove *)
Require Import coherence_leaf.  (* unmap_leaf_mem, leaf_addr_removal_faults,
                                   leaf_addr_none_implies_translate_none *)
Require Import shootdown.       (* core_with_root *)
Require Import ipi.             (* ipi_broadcast_cores, ipi_broadcast_cores_preserves,
                                   ipi_broadcast_cores_spec, sfence_prefix_full,
                                   invalidate_shootdown, invalidate_shootdown_correct,
                                   ipi_root / ipi_va / ipi_stale_core / ipi_flushed_core *)
Require Import machine_encoding. (* invalid_pte (test vectors) *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From stdpp Require Import bitvector.definitions. (* bv_unsigned_inj / bv_unsigned_in_range *)
Require Import mword_lemmas.    (* uint_bv_unsigned, uint_shiftl, uint_or_vec,
                                   uint_zero_extend, Z_lor_add_pow2 *)
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

(* ============================================================
   S4.1c: pte_address injectivity (the deferred "arithmetic opaque" boundary).

   pte_address packs a 44-bit table PPN into bits [55:12] and a 9-bit index
   into bits [11:3] (bits [2:0] are zero).  As a uint this is
   `uint ppn * 2^12 + uint idx * 2^3`, from which injectivity follows: the low
   12 bits recover the index and the high 44 recover the PPN.  This is the
   arithmetic Stage 1 kept opaque (via eq_vec case analysis); it is the missing
   ingredient for the universal `IOTLB ⊆ mapping` invariant, because showing
   that unmapping `va` leaves *other* pages' walks untouched needs
   "different index ⇒ different slot address" for free.
   ============================================================ *)

(* uint is injective on mwords: the concrete MachineWord's bv_unsigned is. *)
Lemma mword_uint_inj {a} (x y : mword a) : uint x = uint y -> x = y.
Proof.
  intro H. apply bv_unsigned_inj.
  rewrite <- !uint_bv_unsigned. exact H.
Qed.

(* uint of an mword is in [0, 2^a): the bv range + the concrete modulus. *)
Lemma mword_uint_range {a} (x : mword a) : 0 <= a -> 0 <= uint x < 2^a.
Proof.
  intro Ha. rewrite uint_bv_unsigned.
  pose proof (bv_unsigned_in_range (Z.to_N a) x) as Hr.
  rewrite (bv_modulus_mword (a := a)) in Hr by lia.
  exact Hr.
Qed.

(* uint is strictly below 2^a (the upper half of mword_uint_range). *)
Lemma uint_lt_pow2 {a} (x : mword a) : 0 <= a -> uint x < 2^a.
Proof.
  intro Ha. pose proof (mword_uint_range x Ha) as Hr. destruct Hr as [_ Hlt]. exact Hlt.
Qed.

(* The small-shift bounds `n < 2^56` (lia cannot unfold the power). *)
Lemma pow2_56_gt_12 : 12 < 2^56.
Proof.
  transitivity 64.
  - lia.
  - replace 64 with (2^6) by (vm_compute; reflexivity).
    apply (Z.pow_lt_mono_r 2 6 56); lia.
Qed.

Lemma pow2_56_gt_3 : 3 < 2^56.
Proof.
  transitivity 8.
  - lia.
  - replace 8 with (2^3) by (vm_compute; reflexivity).
    apply (Z.pow_lt_mono_r 2 3 56); lia.
Qed.

(* The arithmetic content of pte_address: `uint ppn * 2^12 + uint idx * 2^3`.
   The OR is an add because the two shifted fields occupy disjoint bit ranges. *)
Lemma uint_pte_address (ppn : mword 44) (idx : mword 9) :
  uint (pte_address ppn idx) = uint ppn * 2^12 + uint idx * 2^3.
Proof.
  unfold pte_address.
  rewrite uint_or_vec.
  assert (H56 : 0 <= 56) by lia.
  assert (H12 : 0 <= 12 < 2^56) by (split; [lia | apply pow2_56_gt_12]).
  assert (H3 : 0 <= 3 < 2^56) by (split; [lia | apply pow2_56_gt_3]).
  rewrite (uint_shiftl (zero_extend ppn 56) 12 H56 H12).
  rewrite (uint_shiftl (zero_extend idx 56) 3 H56 H3).
  rewrite (uint_zero_extend ppn) by lia.
  rewrite (uint_zero_extend idx) by lia.
  assert (Hp : (uint ppn * 2^12) mod 2^56 = uint ppn * 2^12).
  { apply Z.mod_small. split.
    - apply Z.mul_nonneg_nonneg; [apply uint_nonneg | lia].
    - apply (Z.lt_le_trans (uint ppn * 2^12) (2^44 * 2^12) (2^56)).
      + apply Z.mul_lt_mono_pos_r; [lia | apply uint_lt_pow2; lia].
      + replace (2^44 * 2^12) with (2^56) by (vm_compute; reflexivity). lia. }
  assert (Hi : (uint idx * 2^3) mod 2^56 = uint idx * 2^3).
  { apply Z.mod_small. split.
    - apply Z.mul_nonneg_nonneg; [apply uint_nonneg | lia].
    - apply (Z.lt_le_trans (uint idx * 2^3) (2^9 * 2^3) (2^56)).
      + apply Z.mul_lt_mono_pos_r; [lia | apply uint_lt_pow2; lia].
      + replace (2^9 * 2^3) with (2^12) by (vm_compute; reflexivity).
        apply (Z.pow_le_mono_r 2 12 56); lia. }
  rewrite Hp, Hi.
  rewrite (Z_lor_add_pow2 (uint ppn) 12 (uint idx * 2^3)).
  - reflexivity.
  - apply uint_nonneg.
  - lia.
  - split.
    + apply Z.mul_nonneg_nonneg; [apply uint_nonneg | lia].
    + apply (Z.lt_le_trans (uint idx * 2^3) (2^9 * 2^3) (2^12)).
      * apply Z.mul_lt_mono_pos_r; [lia | apply uint_lt_pow2; lia].
      * replace (2^9 * 2^3) with (2^12) by (vm_compute; reflexivity). lia.
Qed.

(* The low 12 bits of a pte_address are exactly the index's contribution. *)
Lemma low12_of_pte_address (ppn : mword 44) (idx : mword 9) :
  (uint ppn * 2^12 + uint idx * 2^3) mod 2^12 = uint idx * 2^3.
Proof.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_mul by lia.      (* (uint ppn * 2^12) mod 2^12 = 0 *)
  rewrite Z.add_0_l.
  rewrite Z.mod_mod by lia.
  apply Z.mod_small. split.
  - apply Z.mul_nonneg_nonneg; [apply uint_nonneg | lia].
  - apply (Z.lt_le_trans (uint idx * 2^3) (2^9 * 2^3) (2^12)).
    + apply Z.mul_lt_mono_pos_r; [lia | apply uint_lt_pow2; lia].
    + replace (2^9 * 2^3) with (2^12) by (vm_compute; reflexivity). lia.
Qed.

(* pte_address is injective: equal slot addresses have equal PPN and index. *)
Lemma pte_address_injective (ppn ppn' : mword 44) (idx idx' : mword 9) :
  pte_address ppn idx = pte_address ppn' idx' -> ppn = ppn' /\ idx = idx'.
Proof.
  intro H.
  assert (Hu : uint ppn * 2^12 + uint idx * 2^3 = uint ppn' * 2^12 + uint idx' * 2^3)
    by (rewrite <- !uint_pte_address; f_equal; exact H).
  assert (Hidx : uint idx = uint idx').
  { assert (Hmod : (uint ppn * 2^12 + uint idx * 2^3) mod 2^12
                    = (uint ppn' * 2^12 + uint idx' * 2^3) mod 2^12)
      by (rewrite Hu; reflexivity).
    rewrite (low12_of_pte_address ppn idx) in Hmod.
    rewrite (low12_of_pte_address ppn' idx') in Hmod.
    apply (Z.mul_reg_r (uint idx) (uint idx') 8) in Hmod; [exact Hmod | lia]. }
  split.
  - apply mword_uint_inj.
    apply (Z.mul_reg_r (uint ppn) (uint ppn') (2^12)).
    + lia.
    + assert (Hidx8 : uint idx * 2^3 = uint idx' * 2^3) by (f_equal; exact Hidx).
      rewrite Hidx8 in Hu. lia.
  - apply mword_uint_inj. exact Hidx.
Qed.

(* Different index ⇒ different slot address, regardless of the table PPN. *)
Lemma pte_address_neq_index (ppn ppn' : mword 44) (idx idx' : mword 9) :
  idx <> idx' -> pte_address ppn idx <> pte_address ppn' idx'.
Proof.
  intros Hidx Heq. apply Hidx.
  destruct (pte_address_injective ppn ppn' idx idx' Heq) as [_ Hix].
  exact Hix.
Qed.

(* ============================================================
   S4.2a: the functional IOMMU broadcast shootdown over Machine.

   The IOMMU twin of `ipi_broadcast` (ipi.v S2.3b): the leader breaks-before-
   makes the leaf PTE for `va`, invalidates the IOTLB for `va` (the queued
   invalidation + Invalidation-Wait completion), then delivers the IPI to and
   receives the ack from every core (the CPU-TLB flush).  `iommu_shootdown`
   refines `invalidate_shootdown` on the CPU side and additionally drops the
   unmapped page's device translations, so after it: no core translates the
   freed frame, the device walk faults, and no stale IOTLB entry survives.
   ============================================================ *)

(* The break-before-make (write-invalid) device-side twin of [iommu_unmap_faults]. *)
Lemma iommu_invalidate_faults (root : mword 44) (mem : list MemEntry) (va : mword 64) (p : Pte) :
  p.(Pte_valid) = false ->
  iommu_walk root (invalidate_leaf_mem (core_with_root root) mem va p) va = None.
Proof.
  intros Hinv. unfold iommu_walk, invalidate_leaf_mem.
  destruct (leaf_addr (core_with_root root) mem va) as [a |] eqn:Hl.
  - apply (invalidate_leaf_faults (core_with_root root) mem va a p Hl Hinv).
  - apply (leaf_addr_none_implies_translate_none (core_with_root root) mem va Hl).
Qed.

(* The IOMMU broadcast shootdown: break-before-make + IOTLB invalidate + the
   IPI-delivered CPU-TLB flush (reusing ipi.v's `ipi_broadcast_cores`). *)
Definition iommu_shootdown (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) : Machine :=
  let m1 := {| Machine_mem := invalidate_leaf_mem (core_with_root root) m.(Machine_mem) va p;
               Machine_cores := m.(Machine_cores);
               Machine_ram := m.(Machine_ram);
               Machine_ipi := m.(Machine_ipi);
               Machine_iotlb := iotlb_invalidate m.(Machine_iotlb) va; Machine_devtlbs := m.(Machine_devtlbs); Machine_prireqs := m.(Machine_prireqs); Machine_ioqueue := m.(Machine_ioqueue) |} in
  ipi_broadcast_cores m1 (length m.(Machine_cores)) va.

(* ipi_broadcast_cores leaves the IOTLB untouched (deliver_ipi / receive_ipi
   both carry it unchanged), so the invalidation set up in m1 survives the loop. *)
Lemma ipi_broadcast_cores_preserves_iotlb (m : Machine) (n : nat) (va : mword 64) :
  (ipi_broadcast_cores m n va).(Machine_iotlb) = m.(Machine_iotlb).
Proof.
  induction n as [| k IH]; cbn [ipi_broadcast_cores].
  - reflexivity.
  - unfold receive_ipi, deliver_ipi. cbn [Machine_iotlb]. exact IH.
Qed.

(* The IOMMU broadcast's post-IOTLB is exactly the invalidation of the pre-IOTLB. *)
Lemma iommu_shootdown_iotlb (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  (iommu_shootdown m root va p).(Machine_iotlb) = iotlb_invalidate m.(Machine_iotlb) va.
Proof.
  unfold iommu_shootdown.
  rewrite ipi_broadcast_cores_preserves_iotlb. cbn. reflexivity.
Qed.

(* The IOMMU broadcast refines the functional `invalidate_shootdown` on the CPU
   side (same mem, same flushed cores) — the proof is `ipi_broadcast_refines_
   invalidate_shootdown` with the IOTLB already invalidated in the intermediate
   machine (the IOTLB field is never consulted by the cores/mem projections). *)
Lemma iommu_shootdown_refines_invalidate_shootdown
    (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  length m.(Machine_ipi) = length m.(Machine_cores) ->
  (iommu_shootdown m root va p).(Machine_mem) = (invalidate_shootdown m root va p).(Machine_mem) /\
  (iommu_shootdown m root va p).(Machine_cores) = (invalidate_shootdown m root va p).(Machine_cores).
Proof.
  intros Hlen.
  unfold iommu_shootdown.
  set (n := length m.(Machine_cores)).
  set (m1 := {| Machine_mem := invalidate_leaf_mem (core_with_root root) m.(Machine_mem) va p;
                Machine_cores := m.(Machine_cores);
                Machine_ram := m.(Machine_ram);
                Machine_ipi := m.(Machine_ipi);
                Machine_iotlb := iotlb_invalidate m.(Machine_iotlb) va; Machine_devtlbs := m.(Machine_devtlbs); Machine_prireqs := m.(Machine_prireqs); Machine_ioqueue := m.(Machine_ioqueue) |}).
  split.
  - (* mem *)
    destruct (ipi_broadcast_cores_preserves m1 n va) as [Hmem _].
    rewrite Hmem. subst m1 n. cbn.
    unfold invalidate_shootdown. cbn. reflexivity.
  - (* cores *)
    assert (Hcores_bound : Nat.le n (length m1.(Machine_cores))).
    { subst m1 n. cbn. lia. }
    assert (Hipi_bound : Nat.le n (length m1.(Machine_ipi))).
    { subst m1 n. cbn. rewrite Hlen. lia. }
    rewrite (ipi_broadcast_cores_spec m1 n va Hcores_bound Hipi_bound).
    subst m1 n. cbn.
    rewrite sfence_prefix_full.
    unfold invalidate_shootdown. cbn. reflexivity.
Qed.

(* The headline: after the IOMMU broadcast, no core translates the freed frame,
   the device walk faults for it, and no stale device translation survives. *)
Theorem iommu_shootdown_correct (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  p.(Pte_valid) = false ->
  length m.(Machine_ipi) = length m.(Machine_cores) ->
  Forall (fun c => c.(Core_satp_ppn) = root) m.(Machine_cores) ->
  Forall (fun c => translate c (iommu_shootdown m root va p).(Machine_mem) va = None /\
                   tlb_lookup c va = None)
         (iommu_shootdown m root va p).(Machine_cores) /\
  iommu_walk root (iommu_shootdown m root va p).(Machine_mem) va = None /\
  Forall (fun e => vpn_of e.(IotlbEntry_iova) <> vpn_of va)
         (iommu_shootdown m root va p).(Machine_iotlb).
Proof.
  intros Hinv Hlen Hroot.
  destruct (iommu_shootdown_refines_invalidate_shootdown m root va p Hlen) as [Hmem Hcores].
  split; [| split].
  - (* CPU coherence: the CPU side refines invalidate_shootdown. *)
    rewrite Hmem, Hcores.
    apply invalidate_shootdown_correct; assumption.
  - (* device walk faults for the freed frame. *)
    rewrite Hmem. unfold invalidate_shootdown. cbn.
    apply (iommu_invalidate_faults root m.(Machine_mem) va p Hinv).
  - (* no stale IOTLB entry survives. *)
    rewrite iommu_shootdown_iotlb.
    apply iotlb_invalidate_removes.
Qed.

(* ============================================================
   S4.2a executable vector: a 3-core machine with two cached device
   translations — the broadcast flushes every core and drops exactly the
   unmapped page's IOTLB entry.
   ============================================================ *)

Definition iommu_shootdown_machine : Machine :=
  {| Machine_cores := [ipi_stale_core; ipi_stale_core; ipi_stale_core];
     Machine_mem := [];
     Machine_ram := [];
     Machine_ipi := [false; false; false];
     Machine_iotlb := [iommu_e0; iommu_e1]; Machine_devtlbs := []; Machine_prireqs := []; Machine_ioqueue := [] |}.

Lemma test_vector_iommu_shootdown :
  let m' := iommu_shootdown iommu_shootdown_machine ipi_root ipi_va invalid_pte in
  m'.(Machine_ipi) = [true; true; true] /\
  m'.(Machine_cores) = [ipi_flushed_core; ipi_flushed_core; ipi_flushed_core] /\
  m'.(Machine_iotlb) = [iommu_e1].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ============================================================
   S4.1c (universal): the literal `IOTLB ⊆ mapping` invariant, and its
   preservation by unmap+invalidate.  This is what pte_address injectivity
   was for: showing unmapping `va` leaves every *other* page's walk untouched.

   The one real hypothesis is well-formedness: the page table must be a forest
   (no two distinct non-leaf PTEs share a table PPN, and the root is never a
   table PPN).  That rules out table aliasing/cycles, which is exactly the
   case where removing one leaf's PTE could disturb another leaf's walk even
   when the VPNs differ.  A correct kernel's page tables satisfy this.
   ============================================================ *)

(* Bridge to [wf_page_table] (below) for the deferred headline theorem: a read
   that returned a PTE means that PTE is present in the table, turning the walk's
   `read_pte ... = Some p` into the `In {| ... |} mem` premise the forest
   condition quantifies over. *)
Lemma read_pte_Some_In (mem : list MemEntry) (a : mword 56) (p : Pte) :
  read_pte mem a = Some p -> In {| MemEntry_addr := a; MemEntry_pte := p |} mem.
Proof.
  induction mem as [| e rest IH]; cbn [read_pte].
  - discriminate.
  - destruct (eq_vec e.(MemEntry_addr) a) eqn:E.
    + intros H. left.
      apply eq_vec_true_iff in E.
      injection H as Hp.
      destruct e as [addr pte]. cbn in E, Hp.
      rewrite <- E, <- Hp. reflexivity.
    + intros H. right. apply IH. exact H.
Qed.

(* A non-leaf (intermediate) PTE: valid, not a leaf, N clear. *)
Definition is_table (p : Pte) : bool :=
  p.(Pte_valid) && negb (is_leaf p) && negb (p.(Pte_napot)).

(* Well-formed (alias-free) page table: distinct non-leaf PTEs never share a
   table PPN, and no table PPN is the root itself (no cycles). *)
Definition wf_page_table (root : mword 44) (mem : list MemEntry) : Prop :=
  (forall e1 e2, In e1 mem -> In e2 mem ->
     e1.(MemEntry_addr) <> e2.(MemEntry_addr) ->
     is_table e1.(MemEntry_pte) = true -> is_table e2.(MemEntry_pte) = true ->
     e1.(MemEntry_pte).(Pte_ppn) <> e2.(MemEntry_pte).(Pte_ppn))
  /\ (forall e, In e mem -> is_table e.(MemEntry_pte) = true -> e.(MemEntry_pte).(Pte_ppn) <> root).

(* Frame property: removing the entry at `a` leaves va''s walk unchanged when
   all three of its read addresses differ from `a` (the level-1 and level-0
   addresses are conditional on the resolved PTEs, hence the quantifiers). *)
Lemma translate_remove_frame
    (core : Core) (mem : list MemEntry) (va' : mword 64) (a : mword 56) :
  a <> pte_address core.(Core_satp_ppn) (vpn2 va') ->
  (forall p2, read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va')) = Some p2 ->
     is_table p2 = true -> a <> pte_address p2.(Pte_ppn) (vpn1 va')) ->
  (forall p2 p1, read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va')) = Some p2 ->
     is_table p2 = true ->
     read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va')) = Some p1 ->
     is_table p1 = true -> a <> pte_address p1.(Pte_ppn) (vpn0 va')) ->
  translate core (remove_entry mem a) va' = translate core mem va'.
Proof.
  intros Hr2 Hr1 Hr0.
  unfold translate. cbn.
  rewrite (read_pte_remove_other mem a (pte_address core.(Core_satp_ppn) (vpn2 va')) Hr2).
  destruct (read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va'))) as [p2 |] eqn:Hl2.
  - cbn. destruct (p2.(Pte_valid)) eqn:Ev2.
    + cbn. destruct (is_leaf p2) eqn:El2.
      * reflexivity.
      * cbn. destruct (p2.(Pte_napot)) eqn:En2.
        -- reflexivity.
        -- cbn.
           assert (Ht2 : is_table p2 = true)
             by (unfold is_table; rewrite Ev2, El2, En2; reflexivity).
           rewrite (read_pte_remove_other mem a (pte_address p2.(Pte_ppn) (vpn1 va'))).
           { destruct (read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va'))) as [p1 |] eqn:Hl1.
             - cbn. destruct (p1.(Pte_valid)) eqn:Ev1.
               + cbn. destruct (is_leaf p1) eqn:El1.
                 * reflexivity.
                 * cbn. destruct (p1.(Pte_napot)) eqn:En1.
                   -- reflexivity.
                   -- cbn.
                      assert (Ht1 : is_table p1 = true)
                        by (unfold is_table; rewrite Ev1, El1, En1; reflexivity).
                      rewrite (read_pte_remove_other mem a (pte_address p1.(Pte_ppn) (vpn0 va'))).
                      { reflexivity. }
                      { apply (Hr0 p2 p1). reflexivity. exact Ht2. exact Hl1. exact Ht1. }
               + reflexivity.
             - reflexivity. }
           { apply (Hr1 p2). reflexivity. exact Ht2. }
    + reflexivity.
  - reflexivity.
Qed.

(* The literal `IOTLB ⊆ mapping` invariant: every cached device translation
   agrees with the current page table.

   Its preservation by unmap+invalidate is the headline S4.1d theorem
   [iommu_unmap_preserves_coherence] (below): `translate_remove_frame` reduces
   it to three "the removed slot `a` differs from va''s three read addresses"
   facts, each following from `pte_address_injective` plus `wf_page_table`, with
   the level-0 case using the bitvector reconstruction `vpn_of_determined`
   (`vpn_of va` is determined by `(vpn2 va, vpn1 va, vpn0 va)`). *)
Definition iotlb_coherent (root : mword 44) (mem : list MemEntry) (iotlb : list IotlbEntry) : Prop :=
  forall e, In e iotlb -> iommu_walk root mem e.(IotlbEntry_iova) = Some (e.(IotlbEntry_pa), e.(IotlbEntry_perm)).

(* ============================================================
   S4.1d: the bitvector fact that closes the universal invariant.

   `vpn_of` is `va[38..12]`; `vpn2/vpn1/vpn0` are `va[38..30]`,
   `va[29..21]`, `va[20..12]`.  At the uint level each is a quotient/remainder
   of `uint va`; reconstructing the 27-bit VPN from the three 9-bit levels is
   then the pure arithmetic identity
     (x / 2^12) mod 2^27
   = 2^18 · ((x/2^30) mod 2^9) + 2^9 · ((x/2^21) mod 2^9) + ((x/2^12) mod 2^9),
   so `vpn_of va' <> vpn_of va` forces a difference at one of the three levels.
   ============================================================ *)

(* Positive powers of two (the side conditions for div/mod lemmas). *)
Lemma pow2_pos (k : Z) : 0 <= k -> 0 < 2^k.
Proof. intro Hk. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_neq0 (k : Z) : 0 <= k -> 2^k <> 0.
Proof. intro Hk. apply Z.pow_nonzero; lia. Qed.

(* uint of a bit slice `v[hi..lo]` is (uint v / 2^lo) mod 2^(hi-lo+1), for the
   four concrete slices the VPN split uses (concrete widths keep the
   `autocast`/`to_word_idx` plumbing definitional, as in uint_subrange_vec_dec_55_0). *)
Lemma uint_vpn2 (va : mword 64) : uint (vpn2 va) = (uint va / 2^30) mod 2^9.
Proof.
  unfold vpn2, subrange_vec_dec.
  rewrite uint_autocast by reflexivity.
  rewrite uint_to_word_idx.
  unfold MachineWord.slice, MachineWord.word_to_N.
  rewrite Z2N.id by (apply bv_unsigned_in_range).
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite bv_wrap_mword by lia.
  rewrite uint_bv_unsigned.
  reflexivity.
Qed.

Lemma uint_vpn1 (va : mword 64) : uint (vpn1 va) = (uint va / 2^21) mod 2^9.
Proof.
  unfold vpn1, subrange_vec_dec.
  rewrite uint_autocast by reflexivity.
  rewrite uint_to_word_idx.
  unfold MachineWord.slice, MachineWord.word_to_N.
  rewrite Z2N.id by (apply bv_unsigned_in_range).
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite bv_wrap_mword by lia.
  rewrite uint_bv_unsigned.
  reflexivity.
Qed.

Lemma uint_vpn0 (va : mword 64) : uint (vpn0 va) = (uint va / 2^12) mod 2^9.
Proof.
  unfold vpn0, subrange_vec_dec.
  rewrite uint_autocast by reflexivity.
  rewrite uint_to_word_idx.
  unfold MachineWord.slice, MachineWord.word_to_N.
  rewrite Z2N.id by (apply bv_unsigned_in_range).
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite bv_wrap_mword by lia.
  rewrite uint_bv_unsigned.
  reflexivity.
Qed.

Lemma uint_vpn_of (va : mword 64) : uint (vpn_of va) = (uint va / 2^12) mod 2^27.
Proof.
  unfold vpn_of, subrange_vec_dec.
  rewrite uint_autocast by reflexivity.
  rewrite uint_to_word_idx.
  unfold MachineWord.slice, MachineWord.word_to_N.
  rewrite Z2N.id by (apply bv_unsigned_in_range).
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite bv_wrap_mword by lia.
  rewrite uint_bv_unsigned.
  reflexivity.
Qed.

(* The pure reconstruction identity: the low 27 bits of x / 2^12 are assembled
   from the three 9-bit fields [38:30], [29:21], [20:12] of x. *)
Lemma vpn_bits_reconstruct (x : Z) :
  0 <= x ->
  (x / 2^12) mod 2^27 =
  2^18 * ((x / 2^30) mod 2^9) + 2^9 * ((x / 2^21) mod 2^9) + ((x / 2^12) mod 2^9).
Proof.
  intro Hx.
  rewrite !Z.mod_eq by (apply pow2_neq0; lia).
  rewrite (Z.div_div x (2^12) (2^27)) by (first [apply pow2_neq0; lia | apply pow2_pos; lia]).
  rewrite (Z.div_div x (2^30) (2^9)) by (first [apply pow2_neq0; lia | apply pow2_pos; lia]).
  rewrite (Z.div_div x (2^21) (2^9)) by (first [apply pow2_neq0; lia | apply pow2_pos; lia]).
  rewrite (Z.div_div x (2^12) (2^9)) by (first [apply pow2_neq0; lia | apply pow2_pos; lia]).
  replace (2^12 * 2^27) with (2^39) by (vm_compute; reflexivity).
  replace (2^30 * 2^9) with (2^39) by (vm_compute; reflexivity).
  replace (2^21 * 2^9) with (2^30) by (vm_compute; reflexivity).
  replace (2^12 * 2^9) with (2^21) by (vm_compute; reflexivity).
  assert (H18 : 2^18 = 262144) by (vm_compute; reflexivity).
  assert (H9 : 2^9 = 512) by (vm_compute; reflexivity).
  assert (H27 : 2^27 = 134217728) by (vm_compute; reflexivity).
  rewrite H18, H9, H27.
  ring.
Qed.

(* The VPN is determined by its three 9-bit levels: equal levels force equal VPN. *)
Lemma vpn_of_determined (va' va : mword 64) :
  vpn2 va' = vpn2 va -> vpn1 va' = vpn1 va -> vpn0 va' = vpn0 va ->
  vpn_of va' = vpn_of va.
Proof.
  intros H2 H1 H0.
  apply mword_uint_inj.
  rewrite !uint_vpn_of.
  assert (A2 : (uint va' / 2^30) mod 2^9 = (uint va / 2^30) mod 2^9)
    by (apply (f_equal uint) in H2; rewrite !uint_vpn2 in H2; exact H2).
  assert (A1 : (uint va' / 2^21) mod 2^9 = (uint va / 2^21) mod 2^9)
    by (apply (f_equal uint) in H1; rewrite !uint_vpn1 in H1; exact H1).
  assert (A0 : (uint va' / 2^12) mod 2^9 = (uint va / 2^12) mod 2^9)
    by (apply (f_equal uint) in H0; rewrite !uint_vpn0 in H0; exact H0).
  rewrite (vpn_bits_reconstruct (uint va')) by (apply uint_nonneg).
  rewrite A2, A1, A0.
  rewrite <- (vpn_bits_reconstruct (uint va)) by (apply uint_nonneg).
  reflexivity.
Qed.

(* Different table PPN ⇒ different slot address (contrapositive of injectivity). *)
Lemma pte_address_ppn_neq (ppn ppn' : mword 44) (idx idx' : mword 9) :
  ppn <> ppn' -> pte_address ppn idx <> pte_address ppn' idx'.
Proof.
  intros Hppn Heq. apply Hppn.
  destruct (pte_address_injective ppn ppn' idx idx' Heq) as [Hp _].
  exact Hp.
Qed.

(* A survivor of [iotlb_invalidate] is an original entry for a different page. *)
Lemma iotlb_invalidate_In (iotlb : list IotlbEntry) (va : mword 64) (e : IotlbEntry) :
  In e (iotlb_invalidate iotlb va) ->
  In e iotlb /\ vpn_of e.(IotlbEntry_iova) <> vpn_of va.
Proof.
  induction iotlb as [| h t IH]; cbn.
  - intro H; inversion H.
  - destruct (eq_vec (vpn_of h.(IotlbEntry_iova)) (vpn_of va)) eqn:E.
    + (* h dropped *)
      intro H. destruct (IH H) as [Hin Hneq]. split; [right; exact Hin | exact Hneq].
    + (* h kept *)
      intro H. destruct H as [Hh | Ht].
      * subst. split; [left; reflexivity | apply eq_vec_false_iff; exact E].
      * destruct (IH Ht) as [Hin Hneq]. split; [right; exact Hin | exact Hneq].
Qed.

(* The software walk reaching level 0 gives exactly the two intermediate table
   PTEs (both non-leaf, valid, N clear) and the level-0 slot address. *)
Lemma leaf_addr_spec (core : Core) (mem : list MemEntry) (va : mword 64) (a : mword 56) :
  leaf_addr core mem va = Some a ->
  exists p2 p1,
    read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va)) = Some p2 /\
    is_table p2 = true /\
    read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va)) = Some p1 /\
    is_table p1 = true /\
    a = pte_address p1.(Pte_ppn) (vpn0 va).
Proof.
  unfold leaf_addr.
  destruct (read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va))) as [p2 |] eqn:Hl2;
    [| discriminate].
  destruct (p2.(Pte_valid)) eqn:Ev2; [| discriminate].
  destruct (is_leaf p2) eqn:El2; [discriminate |].
  destruct (p2.(Pte_napot)) eqn:En2; [discriminate |].
  destruct (read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va))) as [p1 |] eqn:Hl1;
    [| discriminate].
  destruct (p1.(Pte_valid)) eqn:Ev1; [| discriminate].
  destruct (is_leaf p1) eqn:El1; [discriminate |].
  destruct (p1.(Pte_napot)) eqn:En1; [discriminate |].
  intros Ha. injection Ha as Ha'.
  exists p2, p1.
  split.
  - (* read_pte ... = Some p2, rewritten by the destruct to [Some p2 = Some p2] *)
    reflexivity.
  - split.
    + unfold is_table. rewrite Ev2, El2, En2. reflexivity.
    + split.
      * (* the inner read depends on the (not-yet-unified) existential p2, so it
           was not rewritten by the inner destruct *)
        exact Hl1.
      * split.
        -- unfold is_table. rewrite Ev1, El1, En1. reflexivity.
        -- symmetry. exact Ha'.
Qed.

(* ============================================================
   S4.1d headline: unmap+invalidate preserves `IOTLB ⊆ mapping`.

   For a survivor whose IOVA page differs from the unmapped page, the removed
   leaf slot `a = pte_address p1_va.ppn (vpn0 va)` differs from every slot the
   survivor's walk reads — the root slot (no table PPN is the root), the
   level-1 slot (distinct non-leaf tables have distinct PPNs), and the level-0
   slot (either a different table, or the same table with a different VPN0,
   forced by `vpn_of_determined`).  So `translate_remove_frame` applies and the
   walk is unchanged.  The three facts are the helper lemmas below.
   ============================================================ *)

(* The removed level-0 slot is never the root's level-2 slot. *)
Lemma unmap_slot_neq_root_slot (root : mword 44) (mem : list MemEntry) (va : mword 64)
    (p2_va p1_va : Pte) (va' : mword 64) :
  wf_page_table root mem ->
  read_pte mem (pte_address root (vpn2 va)) = Some p2_va ->
  is_table p2_va = true ->
  read_pte mem (pte_address p2_va.(Pte_ppn) (vpn1 va)) = Some p1_va ->
  is_table p1_va = true ->
  pte_address p1_va.(Pte_ppn) (vpn0 va) <> pte_address root (vpn2 va').
Proof.
  intros Hwf Hp2va Ht2va Hp1va Ht1va.
  destruct Hwf as [Hwf1 Hwf2].
  apply pte_address_ppn_neq.
  apply (Hwf2 {| MemEntry_addr := pte_address p2_va.(Pte_ppn) (vpn1 va); MemEntry_pte := p1_va |}).
  - apply (read_pte_Some_In mem (pte_address p2_va.(Pte_ppn) (vpn1 va)) p1_va Hp1va).
  - exact Ht1va.
Qed.

(* The removed level-0 slot differs from a survivor's level-1 slot. *)
Lemma unmap_slot_neq_level1_slot (root : mword 44) (mem : list MemEntry) (va : mword 64)
    (p2_va p1_va : Pte) (va' : mword 64) (p2 : Pte) :
  wf_page_table root mem ->
  read_pte mem (pte_address root (vpn2 va)) = Some p2_va ->
  is_table p2_va = true ->
  read_pte mem (pte_address p2_va.(Pte_ppn) (vpn1 va)) = Some p1_va ->
  is_table p1_va = true ->
  read_pte mem (pte_address root (vpn2 va')) = Some p2 ->
  is_table p2 = true ->
  pte_address p1_va.(Pte_ppn) (vpn0 va) <> pte_address p2.(Pte_ppn) (vpn1 va').
Proof.
  intros Hwf Hp2va Ht2va Hp1va Ht1va Hre2 Htt2.
  destruct Hwf as [Hwf1 Hwf2].
  apply pte_address_ppn_neq.
  apply (Hwf1
    {| MemEntry_addr := pte_address p2_va.(Pte_ppn) (vpn1 va); MemEntry_pte := p1_va |}
    {| MemEntry_addr := pte_address root (vpn2 va'); MemEntry_pte := p2 |}).
  - apply (read_pte_Some_In mem (pte_address p2_va.(Pte_ppn) (vpn1 va)) p1_va Hp1va).
  - apply (read_pte_Some_In mem (pte_address root (vpn2 va')) p2 Hre2).
  - (* the two tables are at distinct addresses: their table PPNs differ *)
    apply (pte_address_ppn_neq p2_va.(Pte_ppn) root (vpn1 va) (vpn2 va')).
    apply (Hwf2 {| MemEntry_addr := pte_address root (vpn2 va); MemEntry_pte := p2_va |}).
    + apply (read_pte_Some_In mem (pte_address root (vpn2 va)) p2_va Hp2va).
    + exact Ht2va.
  - exact Ht1va.
  - exact Htt2.
Qed.

(* The removed level-0 slot differs from a survivor's level-0 slot.  If the two
   level-0 slots are the same table entry, their VPN0s must differ (forced by
   `vpn_of_determined`, since the survivor's page differs and the upper two
   levels coincide); otherwise the two tables have distinct PPNs. *)
Lemma unmap_slot_neq_level0_slot (root : mword 44) (mem : list MemEntry) (va : mword 64)
    (p2_va p1_va : Pte) (va' : mword 64) (p2 p1 : Pte) :
  wf_page_table root mem ->
  vpn_of va' <> vpn_of va ->
  read_pte mem (pte_address root (vpn2 va)) = Some p2_va ->
  is_table p2_va = true ->
  read_pte mem (pte_address p2_va.(Pte_ppn) (vpn1 va)) = Some p1_va ->
  is_table p1_va = true ->
  read_pte mem (pte_address root (vpn2 va')) = Some p2 ->
  is_table p2 = true ->
  read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va')) = Some p1 ->
  is_table p1 = true ->
  pte_address p1_va.(Pte_ppn) (vpn0 va) <> pte_address p1.(Pte_ppn) (vpn0 va').
Proof.
  intros Hwf Hvpnneq Hp2va Ht2va Hp1va Ht1va Hre2 Htt2 Hre1 Htt1.
  destruct Hwf as [Hwf1 Hwf2].
  destruct (eq_vec (pte_address p2.(Pte_ppn) (vpn1 va')) (pte_address p2_va.(Pte_ppn) (vpn1 va))) eqn:Eslots.
  - (* same level-1 slot: p1 = p1_va; the survivor's VPN0 must differ *)
    apply eq_vec_true_iff in Eslots.
    destruct (pte_address_injective p2.(Pte_ppn) p2_va.(Pte_ppn) (vpn1 va') (vpn1 va) Eslots)
      as [Hppn_eq Hvpn1_eq].
    (* equal level-2 table PPNs force equal level-2 addresses (the forest), hence equal VPN2 *)
    assert (Haddr_eq2 : pte_address root (vpn2 va') = pte_address root (vpn2 va)).
    { destruct (eq_vec (pte_address root (vpn2 va')) (pte_address root (vpn2 va))) eqn:E2;
        [apply eq_vec_true_iff; exact E2 |].
      apply eq_vec_false_iff in E2.
      exfalso.
      exact (Hwf1
        {| MemEntry_addr := pte_address root (vpn2 va'); MemEntry_pte := p2 |}
        {| MemEntry_addr := pte_address root (vpn2 va); MemEntry_pte := p2_va |}
        (read_pte_Some_In mem (pte_address root (vpn2 va')) p2 Hre2)
        (read_pte_Some_In mem (pte_address root (vpn2 va)) p2_va Hp2va)
        E2 Htt2 Ht2va Hppn_eq). }
    destruct (pte_address_injective root root (vpn2 va') (vpn2 va) Haddr_eq2)
      as [_ Hvpn2_eq].
    assert (Hvpn0_neq : vpn0 va' <> vpn0 va).
    { intro Hvpn0_eq. apply Hvpnneq.
      apply (vpn_of_determined va' va Hvpn2_eq Hvpn1_eq Hvpn0_eq). }
    (* p1 = p1_va: rewrite the survivor's level-1 read to the unmapped page's slot *)
    rewrite Hppn_eq in Hre1. rewrite Hvpn1_eq in Hre1.
    assert (Hp1_eq : p1 = p1_va).
    { rewrite Hre1 in Hp1va. injection Hp1va. auto. }
    subst p1.
    apply (pte_address_neq_index p1_va.(Pte_ppn) p1_va.(Pte_ppn) (vpn0 va) (vpn0 va')).
    exact (not_eq_sym Hvpn0_neq).
  - (* different level-1 slot: distinct tables have distinct PPNs *)
    apply eq_vec_false_iff in Eslots.
    apply not_eq_sym.
    apply (pte_address_ppn_neq p1.(Pte_ppn) p1_va.(Pte_ppn) (vpn0 va') (vpn0 va)).
    apply (Hwf1
      {| MemEntry_addr := pte_address p2.(Pte_ppn) (vpn1 va'); MemEntry_pte := p1 |}
      {| MemEntry_addr := pte_address p2_va.(Pte_ppn) (vpn1 va); MemEntry_pte := p1_va |}
      (read_pte_Some_In mem (pte_address p2.(Pte_ppn) (vpn1 va')) p1 Hre1)
      (read_pte_Some_In mem (pte_address p2_va.(Pte_ppn) (vpn1 va)) p1_va Hp1va)
      Eslots Htt1 Ht1va).
Qed.

(* The literal `IOTLB ⊆ mapping` invariant is preserved by unmap+invalidate. *)
Lemma iommu_unmap_preserves_coherence (root : mword 44) (mem : list MemEntry)
    (iotlb : list IotlbEntry) (va : mword 64) :
  iotlb_coherent root mem iotlb ->
  wf_page_table root mem ->
  iotlb_coherent root (unmap_leaf_mem (core_with_root root) mem va) (iotlb_invalidate iotlb va).
Proof.
  intros Hcoh Hwf e Hin.
  destruct (iotlb_invalidate_In iotlb va e Hin) as [Hin' Hvpnneq].
  specialize (Hcoh e Hin').
  unfold iommu_walk in *. unfold unmap_leaf_mem.
  destruct (leaf_addr (core_with_root root) mem va) as [a |] eqn:Hleaf.
  - (* the leaf slot resolved: unmap removes it; the survivor's walk is unchanged *)
    destruct (leaf_addr_spec (core_with_root root) mem va a Hleaf)
      as (p2_va & p1_va & Hp2va & Ht2va & Hp1va & Ht1va & Ha).
    cbn [Core_satp_ppn] in Hp2va.
    assert (Hframe : translate (core_with_root root) (remove_entry mem a) e.(IotlbEntry_iova)
                     = translate (core_with_root root) mem e.(IotlbEntry_iova)).
    { apply (translate_remove_frame (core_with_root root) mem e.(IotlbEntry_iova) a).
      - (* a <> root slot of e.iova *)
        cbn [Core_satp_ppn]. rewrite Ha.
        apply (unmap_slot_neq_root_slot root mem va p2_va p1_va e.(IotlbEntry_iova)
          Hwf Hp2va Ht2va Hp1va Ht1va).
      - (* a <> level-1 slot of e.iova *)
        cbn [Core_satp_ppn]. intros p2 Hre2 Htt2. rewrite Ha.
        apply (unmap_slot_neq_level1_slot root mem va p2_va p1_va e.(IotlbEntry_iova) p2
          Hwf Hp2va Ht2va Hp1va Ht1va Hre2 Htt2).
      - (* a <> level-0 slot of e.iova *)
        cbn [Core_satp_ppn]. intros p2 p1 Hre2 Htt2 Hre1 Htt1. rewrite Ha.
        apply (unmap_slot_neq_level0_slot root mem va p2_va p1_va e.(IotlbEntry_iova) p2 p1
          Hwf Hvpnneq Hp2va Ht2va Hp1va Ht1va Hre2 Htt2 Hre1 Htt1). }
    unfold core_with_root in Hframe.
    rewrite Hframe. exact Hcoh.
  - (* no leaf slot: unmap is a no-op *)
    exact Hcoh.
Qed.

(* ============================================================
   S4.3 (ATS/PRI device side) — executable vectors for the model.
   ats_translate fills the IOTLB + the device-TLB on a walk hit and nothing on
   a fault; ats_invalidate is the per-device tier of the shootdown; pri_request
   enqueues at most one page request per (did, iova).
   ============================================================ *)

Definition ats_ptr_pte (next : mword 44) : Pte :=
  {| Pte_valid := true; Pte_read := false; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.
Definition ats_ro_pte (next : mword 44) : Pte :=
  {| Pte_valid := true; Pte_read := true; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.

Definition ats_dev0 : DevTlbEntry :=
  {| DevTlbEntry_did := 0; DevTlbEntry_iova := (mword_of_int 0 : mword 64);
     DevTlbEntry_pa := (mword_of_int 0 : mword 56); DevTlbEntry_perm := ReadWrite |}.
Definition ats_dev1 : DevTlbEntry :=
  {| DevTlbEntry_did := 0; DevTlbEntry_iova := (mword_of_int 4096 : mword 64);
     DevTlbEntry_pa := (mword_of_int 4096 : mword 56); DevTlbEntry_perm := ReadWrite |}.

(* A three-level table mapping IOVA 0 -> leaf_ppn (read-only), for the ATS hit. *)
Definition ats_table : PageTable :=
  [ {| MemEntry_addr := pte_address (mword_of_int 1 : mword 44) (vpn2 (mword_of_int 0 : mword 64));
       MemEntry_pte := ats_ptr_pte (mword_of_int 2 : mword 44) |};
    {| MemEntry_addr := pte_address (mword_of_int 2 : mword 44) (vpn1 (mword_of_int 0 : mword 64));
       MemEntry_pte := ats_ptr_pte (mword_of_int 3 : mword 44) |};
    {| MemEntry_addr := pte_address (mword_of_int 3 : mword 44) (vpn0 (mword_of_int 0 : mword 64));
       MemEntry_pte := ats_ro_pte (mword_of_int 42 : mword 44) |} ].

(* ATS translation request -> completion: a walk hit fills both caches. *)
Lemma test_vector_ats_translate_hit :
  ats_translate [] [] (mword_of_int 1 : mword 44) 0 (mword_of_int 0 : mword 64) ats_table
  = ([ {| IotlbEntry_did := 0; IotlbEntry_pasid := 0;
          IotlbEntry_iova := (mword_of_int 0 : mword 64);
          IotlbEntry_pa := phys_addr (mword_of_int 42 : mword 44) (page_offset (mword_of_int 0 : mword 64));
          IotlbEntry_perm := Read |} ],
     [ {| DevTlbEntry_did := 0; DevTlbEntry_iova := (mword_of_int 0 : mword 64);
          DevTlbEntry_pa := phys_addr (mword_of_int 42 : mword 44) (page_offset (mword_of_int 0 : mword 64));
          DevTlbEntry_perm := Read |} ]).
Proof. vm_compute. reflexivity. Qed.

(* A walk fault caches nothing (the device issues a PRI request instead). *)
Lemma test_vector_ats_translate_fault :
  ats_translate [] [] (mword_of_int 1 : mword 44) 0 (mword_of_int 0 : mword 64) []
  = ([], []).
Proof. vm_compute. reflexivity. Qed.

(* ATS device-TLB invalidation drops the unmapped page's entries, keeps others. *)
Lemma test_vector_ats_invalidate :
  ats_invalidate [ats_dev0; ats_dev1] (mword_of_int 0 : mword 64) = [ats_dev1].
Proof. vm_compute. reflexivity. Qed.

(* PRI page request: enqueue, and dedup at most one pending per (did, iova). *)
Lemma test_vector_pri_request_enqueue :
  pri_request [] 0 (mword_of_int 4096 : mword 64)
  = [{| PriRequest_did := 0; PriRequest_iova := (mword_of_int 4096 : mword 64) |}].
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pri_request_dedup :
  pri_request [{| PriRequest_did := 0; PriRequest_iova := (mword_of_int 4096 : mword 64) |}]
    0 (mword_of_int 4096 : mword 64)
  = [{| PriRequest_did := 0; PriRequest_iova := (mword_of_int 4096 : mword 64) |}].
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   S4.3 (ATS/PRI device side) — the proofs, beyond the executable vectors.

   The ATS completion's (pa, perm) is exactly the walk's (nothing cached the
   walk did not produce); a fault caches nothing (the device issues a PRI page
   request instead); the ATS device-TLB invalidation drops exactly the unmapped
   page's entries (the per-device tier of the shootdown, twin of
   [iotlb_invalidate_removes]); and PRI dedups — a page request is serviced at
   most once per (did, iova).
   ============================================================ *)

(* ATS translation request -> completion: on a walk hit the newly cached IOTLB
   entry and the device-TLB entry carry exactly the walk's (pa, perm). *)
Lemma ats_translate_spec (iotlb : list IotlbEntry) (devtlbs : list DevTlbEntry)
    (root : mword 44) (did : Z) (iova : mword 64) (mem : list MemEntry)
    (pa : mword 56) (perm : Perm) :
  iommu_walk root mem iova = Some (pa, perm) ->
  ats_translate iotlb devtlbs root did iova mem
  = ({| IotlbEntry_did := did; IotlbEntry_pasid := 0; IotlbEntry_iova := iova;
        IotlbEntry_pa := pa; IotlbEntry_perm := perm |} :: iotlb,
     {| DevTlbEntry_did := did; DevTlbEntry_iova := iova;
        DevTlbEntry_pa := pa; DevTlbEntry_perm := perm |} :: devtlbs).
Proof. intros H. unfold ats_translate. rewrite H. reflexivity. Qed.

(* A walk fault caches nothing: the completion is absent and both caches are
   unchanged (the device issues a PRI page request instead). *)
Lemma ats_translate_fault (iotlb : list IotlbEntry) (devtlbs : list DevTlbEntry)
    (root : mword 44) (did : Z) (iova : mword 64) (mem : list MemEntry) :
  iommu_walk root mem iova = None ->
  ats_translate iotlb devtlbs root did iova mem = (iotlb, devtlbs).
Proof. intros H. unfold ats_translate. rewrite H. reflexivity. Qed.

(* ATS device-TLB invalidation: every surviving device-TLB entry is for a
   different page than the unmapped va (the per-device twin of
   [iotlb_invalidate_removes]). *)
Lemma ats_invalidate_removes (devtlbs : list DevTlbEntry) (va : mword 64) :
  Forall (fun e => vpn_of e.(DevTlbEntry_iova) <> vpn_of va) (ats_invalidate devtlbs va).
Proof.
  induction devtlbs as [| e rest IH]; cbn.
  - constructor.
  - destruct (eq_vec (vpn_of e.(DevTlbEntry_iova)) (vpn_of va)) eqn:E.
    + exact IH.
    + constructor.
      * apply eq_vec_false_iff. exact E.
      * exact IH.
Qed.

(* PRI dedup: a device retries the same fault and re-issues the page request;
   the pending set is unchanged.  This is "serviced at most once per fault" —
   enqueueing is idempotent on the (did, iova) key. *)
Lemma pri_request_idempotent (prireqs : list PriRequest) (did : Z) (iova : mword 64) :
  pri_request (pri_request prireqs did iova) did iova = pri_request prireqs did iova.
Proof.
  induction prireqs as [| r rest IH]; cbn.
  - (* []: the fresh request is enqueued, then the re-request finds it. *)
    assert (Ed : Z.eqb did did = true) by (apply (Z.eqb_eq did did); reflexivity).
    assert (Ei : eq_vec iova iova = true) by (apply eq_vec_true_iff; reflexivity).
    rewrite Ed, Ei. reflexivity.
  - destruct (Z.eqb r.(PriRequest_did) did) eqn:Ed;
    destruct (eq_vec r.(PriRequest_iova) iova) eqn:E; cbn.
    + (* (did,iova) matches: both calls return prireqs unchanged. *)
      rewrite Ed, E. reflexivity.
    + (* did matches, iova differs: keep r, recurse. *)
      rewrite Ed, E. rewrite IH. reflexivity.
    + (* did differs, iova matches: keep r, recurse. *)
      rewrite Ed, E. rewrite IH. reflexivity.
    + (* neither matches: keep r, recurse. *)
      rewrite Ed, E. rewrite IH. reflexivity.
Qed.

(* ============================================================
   S4.2b-1 (the command queue, functional): the queued-invalidation
   formulation of the S4.2a broadcast.

   machine.sail's S4.2b-1 additions: `InvalidationCmd` (a queued-invalidation
   descriptor — `IotlbInvalidate va` or `InvalidationWait`) + `Machine_ioqueue`
   (the command queue) + `iommu_process_queue` (drain the FIFO, applying each
   invalidate to the IOTLB, completing `Some iotlb` at the Invalidation-Wait).
   This section proves the queue formulation of S4.2a's
   `iommu_shootdown_correct`: unmap → enqueue Invalidate + Wait → drain ⇒ every
   cached translation for `va` is gone.
   ============================================================ *)

(* The two-descriptor queue: invalidate va, then wait (the completion barrier). *)
Definition invalidate_wait_queue (va : mword 64) : list InvalidationCmd :=
  [ {| InvalidationCmd_is_wait := false; InvalidationCmd_va := va |};
    {| InvalidationCmd_is_wait := true;  InvalidationCmd_va := va |} ].

(* Draining [Invalidate va; Wait] applies exactly one invalidation and then
   completes with the invalidated IOTLB. *)
Lemma iommu_process_queue_spec (iotlb : list IotlbEntry) (va : mword 64) :
  iommu_process_queue (invalidate_wait_queue va) iotlb = Some (iotlb_invalidate iotlb va).
Proof. cbn. reflexivity. Qed.

(* The IOMMU shootdown, queue formulation: break-before-make + enqueue
   Invalidate+Wait + drain.  The drained IOTLB is the invalidation of the
   pre-shootdown IOTLB; the queue itself is emptied by the drain. *)
Definition iommu_shootdown_via_queue (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) : Machine :=
  let mem' := invalidate_leaf_mem (core_with_root root) m.(Machine_mem) va p in
  match iommu_process_queue (invalidate_wait_queue va) m.(Machine_iotlb) with
  | None => m   (* no wait descriptor: no completion, IOTLB unchanged *)
  | Some iotlb' =>
      {| Machine_cores := m.(Machine_cores);
         Machine_mem := mem';
         Machine_ram := m.(Machine_ram);
         Machine_ipi := m.(Machine_ipi);
         Machine_iotlb := iotlb';
         Machine_devtlbs := m.(Machine_devtlbs);
         Machine_prireqs := m.(Machine_prireqs);
         Machine_ioqueue := [] |}
  end.

(* The queue-based shootdown's mem is the break-before-make (write-invalid). *)
Lemma iommu_shootdown_via_queue_mem (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  (iommu_shootdown_via_queue m root va p).(Machine_mem)
  = invalidate_leaf_mem (core_with_root root) m.(Machine_mem) va p.
Proof. unfold iommu_shootdown_via_queue. rewrite iommu_process_queue_spec. cbn. reflexivity. Qed.

(* The queue-based shootdown's IOTLB is exactly the invalidation of the pre-IOTLB. *)
Lemma iommu_shootdown_via_queue_iotlb (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  (iommu_shootdown_via_queue m root va p).(Machine_iotlb)
  = iotlb_invalidate m.(Machine_iotlb) va.
Proof. unfold iommu_shootdown_via_queue. rewrite iommu_process_queue_spec. cbn. reflexivity. Qed.

(* The headline: after the queue-based shootdown, the device walk faults for the
   freed frame and no stale IOTLB entry survives — the queue formulation of
   `iommu_shootdown_correct` (S4.2a). *)
Theorem iommu_shootdown_via_queue_correct (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  p.(Pte_valid) = false ->
  iommu_walk root (iommu_shootdown_via_queue m root va p).(Machine_mem) va = None /\
  Forall (fun e => vpn_of e.(IotlbEntry_iova) <> vpn_of va)
         (iommu_shootdown_via_queue m root va p).(Machine_iotlb).
Proof.
  intros Hinv. split.
  - rewrite iommu_shootdown_via_queue_mem.
    apply (iommu_invalidate_faults root m.(Machine_mem) va p Hinv).
  - rewrite iommu_shootdown_via_queue_iotlb.
    apply (iotlb_invalidate_removes m.(Machine_iotlb) va).
Qed.

(* Executable vector: draining [Invalidate 0; Wait] over a two-entry IOTLB drops
   the IOVA-0 entry and keeps the IOVA-4096 one. *)
Lemma test_vector_iommu_process_queue :
  iommu_process_queue (invalidate_wait_queue (mword_of_int 0 : mword 64)) [iommu_e0; iommu_e1]
  = Some [iommu_e1].
Proof. vm_compute. reflexivity. Qed.

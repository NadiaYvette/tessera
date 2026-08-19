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
               Machine_iotlb := iotlb_invalidate m.(Machine_iotlb) va |} in
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
                Machine_iotlb := iotlb_invalidate m.(Machine_iotlb) va |}).
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
     Machine_iotlb := [iommu_e0; iommu_e1] |}.

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

   NOTE (deferred): its preservation by unmap+invalidate —
   `iotlb_coherent root mem iotlb -> iotlb_coherent root
   (unmap_leaf_mem (core_with_root root) mem va) (iotlb_invalidate iotlb va)` —
   is the headline S4.1c theorem.  `translate_remove_frame` (above) already
   reduces it to three "the removed slot `a` differs from va''s three read
   addresses" facts, each of which follows from `pte_address_injective` plus
   `wf_page_table`.  The remaining missing ingredient is a pure bitvector lemma
   that `vpn_of va` is determined by `(vpn2 va, vpn1 va, vpn0 va)` (i.e.
   `vpn_of = concat(vpn2, vpn1, vpn0)`), so that `vpn_of va' <> vpn_of va`
   forces a difference at one of the three levels — the analogue of Stage 1's
   "keep the arithmetic opaque" boundary, deferred to the next increment. *)
Definition iotlb_coherent (root : mword 44) (mem : list MemEntry) (iotlb : list IotlbEntry) : Prop :=
  forall e, In e iotlb -> iommu_walk root mem e.(IotlbEntry_iova) = Some (e.(IotlbEntry_pa), e.(IotlbEntry_perm)).

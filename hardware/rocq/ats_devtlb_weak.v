(* Tessera — SSG-4 / S4.5: the ATS device-TLB gpfsl lift — the weak-memory
   (gpfsl) program over the endpoint device-TLB invalidation + retranslate
   cycle.

   The functional base is the S4.3 ATS device side (iommu_proofs.v): an ATS
   translation request walks the shared page table (`iommu_walk`); on a hit the
   IOMMU caches the completion in its IOTLB *and* fills the device's device-TLB
   (`ats_translate`, the per-device twin of the core TLB); a walk fault caches
   nothing (the device issues a PRI page request instead, `ats_translate_fault`).
   The ATS device-TLB invalidation (`ats_invalidate`, PCIe ATS §4.3 / SMMU §4.5
   / AMD-Vi §2.11) drops exactly the unmapped page's entries
   (`ats_invalidate_removes`), so after it `find_devtlb` faults for the freed
   frame (`find_devtlb_after_ats_invalidate`) — the "no device translates the
   freed frame" claim of `iommu_shootdown_ats`.

   This file lifts the *invalidate-then-retranslate* cycle to genuine weak
   memory, exactly as `smmu_translate_weak.v` / `amdvi_translate_weak.v` /
   `pasid_translate_weak.v` lift the IOMMU-cache loops: the leader (kernel /
   IOMMU driver) RELEASES the invalidation doorbell and the device ACQUIREs it
   before its request is served — the same release/acquire ordering core as
   S4.2b-2's `iommu_broadcast` — and at the leader's final read the device-TLB
   ghost steps from the *invalidated* cache (after the 4KiB ATS invalidation of
   the page) to the *refilled* one: the ghost post-state is exactly
   `snd (ats_translate iotlb (ats_invalidate devtlbs va) root did va mem)`,
   justified at the pure level by `ats_translate_spec` (on a walk hit the
   freshly cached device-TLB entry carries exactly the walk's (pa, perm)) and
   `ats_devtlb_refill_spec` below.  The ghost `dt_ctx` is a fresh `ghost_var`
   over `list DevTlbEntry` — the endpoint's translation cache, the third tier
   of the shootdown (core TLB, IOTLB, device-TLB).

   As in the cache lifts, the lift reuses
   `iommu_broadcast_full_gen_inv_update` (the generic R ⊢ |==> R' composition
   from S4.2b-2) with R / R' instantiated to the device-TLB ghost;
   `ats_devtlb_dt_machine` threads it alongside the machine ghost, so the
   post-state carries both the ATS machine shootdown (`iommu_shootdown_ats`)
   and the refilled device-TLB. *)

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import lifting proofmode atomics view_invariants
                                 repeat_loop new_delete.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import own ghost_var.
From iris.proofmode Require Import proofmode monpred.
From gpfsl.base_logic Require Import vprop.
From SailStdpp Require Import MachineWord.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.          (* Machine, DevTlbEntry *)
Require Import machine.                (* ats_translate, ats_invalidate *)
Require Import shootdown_weak_broadcast. (* machine_ctx, bcG, machine_ctx_update, UTok, uniqTokG *)
Require Import iommu_proofs.           (* ats_translate_spec, iommu_shootdown_ats *)
Require Import iommu_broadcast_weak.   (* iommu_broadcast, iommu_broadcast_full_gen_inv_update *)
Require Import iris.prelude.options.

(* ============================================================
   Ghost state: the endpoint's device-TLB.  The machine ghost (bcG /
   machine_ctx) comes from shootdown_weak_broadcast; `dt_ctx` is a fresh
   ghost_var over the device's translation cache, stepped at the leader's
   final read from the invalidated cache (after the ATS invalidation of the
   page) to the refilled one (the device re-issued its ATS request).
   ============================================================ *)

Class dtG Σ := DtG { dt_devtlbG : ghost_varG Σ (list DevTlbEntry); }.
Local Existing Instances dt_devtlbG.
Definition dtΣ : gFunctors := #[ghost_varΣ (list DevTlbEntry)].
Global Instance subG_dtΣ {Σ} : subG dtΣ Σ → dtG Σ.
Proof. solve_inG. Qed.

(* The device-TLB ghost, embedded into gpfsl's vProp. *)
Definition dt_ctx `{!dtG Σ} (γd : gname) (d : list DevTlbEntry) : vProp Σ :=
  ⎡ ghost_var γd (DfracOwn 1) d ⎤.

#[global] Instance dt_ctx_objective `{!dtG Σ} γd d : Objective (dt_ctx γd d).
Proof. rewrite /dt_ctx. apply _. Qed.

(* The leader owns the device-TLB ghost exclusively, so it may step it to any
   value; faithfulness (the ghost always matches the constrained physical
   cache) is by construction of the proof, exactly as in S2.1's Honesty note
   and the S4.2b-2 machine corollary. *)
Lemma dt_ctx_update `{!dtG Σ} (γd : gname) (c c' : list DevTlbEntry) :
  dt_ctx γd c ⊢ |==> dt_ctx γd c' : vProp Σ.
Proof.
  rewrite /dt_ctx. iIntros "Hc".
  iMod (ghost_var_update c' γd c with "Hc") as "Hc'".
  iIntros "!>". by iFrame.
Qed.

(* ============================================================
   The pure refill: on a walk hit the device's re-issued ATS request refills
   the device-TLB with exactly the walk's completion — the freshly cached
   entry carries (did, iova, pa, perm).  This is the pure content the lift's
   ghost step stands for: the invalidated cache is *refilled*, so the device
   can translate the page again (now against the new mapping).
   ============================================================ *)

Lemma ats_devtlb_refill_spec (iotlb : list IotlbEntry) (devtlbs : list DevTlbEntry)
    (root : mword 44) (did : Z) (va : mword 64) (mem : list MemEntry)
    (pa : mword 56) (perm : Perm) :
  iommu_walk root mem va = Some (pa, perm) ->
  snd (ats_translate iotlb (ats_invalidate devtlbs va) root did va mem)
  = {| DevTlbEntry_did := did; DevTlbEntry_iova := va;
       DevTlbEntry_pa := pa; DevTlbEntry_perm := perm |} :: ats_invalidate devtlbs va.
Proof.
  intros H.
  pose proof (ats_translate_spec iotlb (ats_invalidate devtlbs va)
                root did va mem pa perm H) as Hs.
  exact (f_equal snd Hs).
Qed.

(* ============================================================
   The lift: the same two release/acquire pairs as S4.2b-2's `iommu_broadcast`
   (the invalidation doorbell and the completion), with R / R' instantiated
   to the device-TLB ghost.  The pre-state is the cache *after the ATS
   invalidation of the page* (the device-TLB is empty of the page's entries)
   and the post-state is the *refilled* cache — the invalidate-then-
   retranslate cycle's cache result.
   ============================================================ *)

Lemma ats_devtlb_dt_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !dtG Σ}
    (γd : gname) (iotlb : list IotlbEntry) (devtlbs : list DevTlbEntry)
    (root : mword 44) (did : Z) (va : mword 64) (mem : list MemEntry) :
  ∀ tid, {{{ dt_ctx γd (ats_invalidate devtlbs va) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ dt_ctx γd (snd (ats_translate iotlb
                                        (ats_invalidate devtlbs va) root did va mem)) }}}.
Proof.
  iIntros (tid Φ) "Hc Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (dt_ctx γd (ats_invalidate devtlbs va))
            (dt_ctx γd (snd (ats_translate iotlb
                              (ats_invalidate devtlbs va) root did va mem))) _ tid
            with "Hc").
  - iIntros (v) "(Hv & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (dt_ctx_update γd (ats_invalidate devtlbs va)
           (snd (ats_translate iotlb (ats_invalidate devtlbs va) root did va mem))).
Qed.

(* The combined update: both ghosts step together (the machine to the ATS
   shootdown — cores/IOTLB cleared *and* the device-TLB ATS-invalidated — and
   the device-TLB ghost to the refilled cache). *)
Lemma dt_machine_update `{!bcG Σ, !dtG Σ} (γm γd : gname) (m m' : Machine)
    (c c' : list DevTlbEntry) :
  (machine_ctx γm m ∗ dt_ctx γd c) ⊢ |==> (machine_ctx γm m' ∗ dt_ctx γd c') : vProp Σ.
Proof.
  iIntros "[Hm Hc]".
  iMod (machine_ctx_update γm m m' with "Hm") as "Hm'".
  iMod (dt_ctx_update γd c c' with "Hc") as "Hc'".
  iIntros "!>". iFrame.
Qed.

(* The machine-aware composition: the leader owns both ghosts exclusively and
   advances them — the machine to the functional ATS shootdown and the
   device-TLB to the retranslate refill — while the final read is still the
   program's step (inside the WP), not in a postcondition adapter. *)
Lemma ats_devtlb_dt_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !dtG Σ}
    (γm γd : gname) (m : Machine) (root : mword 44) (va : mword 64) (p : Pte)
    (iotlb : list IotlbEntry) (did : Z) (mem : list MemEntry) :
  ∀ tid, {{{ machine_ctx γm m ∗ dt_ctx γd (ats_invalidate m.(Machine_devtlbs) va) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm (iommu_shootdown_ats m root va p)
                    ∗ dt_ctx γd (snd (ats_translate iotlb
                                      (ats_invalidate m.(Machine_devtlbs) va) root did va mem)) }}}.
Proof.
  iIntros (tid Φ) "Hm Post".
  iDestruct "Hm" as "[Hm Hc]".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ dt_ctx γd (ats_invalidate m.(Machine_devtlbs) va))
            (machine_ctx γm (iommu_shootdown_ats m root va p) ∗
             dt_ctx γd (snd (ats_translate iotlb
                               (ats_invalidate m.(Machine_devtlbs) va) root did va mem))) _ tid
            with "[$Hm $Hc]").
  - iIntros (v) "(Hv & Hm' & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (dt_machine_update γm γd m (iommu_shootdown_ats m root va p)
           (ats_invalidate m.(Machine_devtlbs) va)
           (snd (ats_translate iotlb (ats_invalidate m.(Machine_devtlbs) va) root did va mem))).
Qed.

(* ============================================================
   The ATS *translation* path (the device-side fill-on-miss) as a weak
   program: where the lifts above are the invalidate-then-retranslate cycle
   (pre = the ATS-invalidated cache, post = the refilled one), this lift is
   the translation itself — an ATS request arriving against the shared page
   table fills the device-TLB on a walk hit (the device-side fill-on-miss)
   and caches nothing on a fault (the device issues a PRI page request
   instead).  The devtlb ghost steps from the pre-translation cache to the
   post-translation one at the leader's final read.
   ============================================================ *)

(* The pure fill: on a walk hit the device-TLB is refilled with exactly the
   walk's completion — the fresh entry carries (did, iova, pa, perm).  This is
   the snd-projection of `ats_translate_spec` (the IOTLB half is the fst). *)
Lemma ats_translate_refills_devtlb (iotlb : list IotlbEntry) (devtlbs : list DevTlbEntry)
    (root : mword 44) (did : Z) (iova : mword 64) (mem : list MemEntry)
    (pa : mword 56) (perm : Perm) :
  iommu_walk root mem iova = Some (pa, perm) ->
  snd (ats_translate iotlb devtlbs root did iova mem)
  = {| DevTlbEntry_did := did; DevTlbEntry_iova := iova;
       DevTlbEntry_pa := pa; DevTlbEntry_perm := perm |} :: devtlbs.
Proof.
  intros H.
  pose proof (ats_translate_spec iotlb devtlbs root did iova mem pa perm H) as Hs.
  exact (f_equal snd Hs).
Qed.

(* The pure fault: on a walk fault the device-TLB is untouched (the device
   issues a PRI page request instead) — the snd-projection of
   `ats_translate_fault`. *)
Lemma ats_translate_fault_devtlb (iotlb : list IotlbEntry) (devtlbs : list DevTlbEntry)
    (root : mword 44) (did : Z) (iova : mword 64) (mem : list MemEntry) :
  iommu_walk root mem iova = None ->
  snd (ats_translate iotlb devtlbs root did iova mem) = devtlbs.
Proof.
  intros H.
  pose proof (ats_translate_fault iotlb devtlbs root did iova mem H) as Hs.
  exact (f_equal snd Hs).
Qed.

(* The translation-path lift: the same release/acquire program, with the
   devtlb ghost stepped from the pre-translation cache to the post-translation
   (refilled-on-hit) one — the device-side fill-on-miss. *)
Lemma ats_translate_dt_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !dtG Σ}
    (γd : gname) (iotlb : list IotlbEntry) (devtlbs : list DevTlbEntry)
    (root : mword 44) (did : Z) (iova : mword 64) (mem : list MemEntry) :
  ∀ tid, {{{ dt_ctx γd devtlbs }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ dt_ctx γd (snd (ats_translate iotlb devtlbs root did iova mem)) }}}.
Proof.
  iIntros (tid Φ) "Hc Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (dt_ctx γd devtlbs)
            (dt_ctx γd (snd (ats_translate iotlb devtlbs root did iova mem))) _ tid
            with "Hc").
  - iIntros (v) "(Hv & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (dt_ctx_update γd devtlbs (snd (ats_translate iotlb devtlbs root did iova mem))).
Qed.

(* The machine-aware translation lift: the devtlb ghost advances alongside the
   machine ghost to the *translated* machine (the ATS request's walk result is
   not a machine mutation — the device-side fill is the only change, carried
   by the devtlb ghost). *)
Lemma ats_translate_dt_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !dtG Σ}
    (γm γd : gname) (m : Machine) (iotlb : list IotlbEntry)
    (root : mword 44) (did : Z) (iova : mword 64) (mem : list MemEntry) :
  ∀ tid, {{{ machine_ctx γm m ∗ dt_ctx γd m.(Machine_devtlbs) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm m
                    ∗ dt_ctx γd (snd (ats_translate iotlb m.(Machine_devtlbs) root did iova mem)) }}}.
Proof.
  iIntros (tid Φ) "[Hm Hc] Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ dt_ctx γd m.(Machine_devtlbs))
            (machine_ctx γm m ∗
             dt_ctx γd (snd (ats_translate iotlb m.(Machine_devtlbs) root did iova mem))) _ tid
            with "[$Hm $Hc]").
  - iIntros (v) "(Hv & Hm' & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (dt_machine_update γm γd m m m.(Machine_devtlbs)
           (snd (ats_translate iotlb m.(Machine_devtlbs) root did iova mem))).
Qed.

(* The fault path is silent at the device-TLB level: a walk fault caches
   nothing, so the devtlb ghost is the identity update (the device issues a
   PRI page request instead — the S4.3 fault path, whose weak delivery is the
   `pri_fault_intc_weak.v` program). *)
Lemma ats_translate_fault_dt_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !dtG Σ}
    (γd : gname) (iotlb : list IotlbEntry) (devtlbs : list DevTlbEntry)
    (root : mword 44) (did : Z) (iova : mword 64) (mem : list MemEntry) :
  iommu_walk root mem iova = None ->
  ∀ tid, {{{ dt_ctx γd devtlbs }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ dt_ctx γd devtlbs }}}.
Proof.
  iIntros (Hfault tid Φ) "Hc Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (dt_ctx γd devtlbs) (dt_ctx γd devtlbs) _ tid
            with "Hc").
  - iIntros (v) "(Hv & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (dt_ctx_update γd devtlbs devtlbs).
Qed.

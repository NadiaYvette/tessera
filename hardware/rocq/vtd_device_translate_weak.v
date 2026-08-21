(* Tessera — SSG-4 / S4.5: the device-side PASID-cache gpfsl lift — the
   weak-memory (gpfsl) program over the device-table fill-on-miss loop.

   The functional base is `vtd_device_translate_fill` (machine.sail, proved in
   vtd_proofs.v): the translation service loop *over the device table*.  The
   PASID cache is keyed by the *DTE's* DID (`pasid_cache_lookup cache
   (d.(VtdDeviceEntry_did), pasid)`), so after an eviction of that DID the
   loop recovers — it re-walks the device's PASID table (selected by the
   DTE's `pasid_tbl` pointer), refills the cache under (d.did, pasid), and
   answers with the device-table walk (`vtd_device_translate_fill_after_evict`,
   with the refilled entry carrying the DTE's DID by
   `vtd_device_translate_fill_refill_tagged`).

   This file lifts that loop to genuine weak memory, exactly as
   `pasid_translate_weak.v` lifts the requester-ID-keyed loop: the leader
   (kernel / IOMMU driver) RELEASES the invalidation doorbell and the IOMMU
   ACQUIREs it before reading the request — the same release/acquire ordering
   core as S4.2b-2's `iommu_broadcast` — and at the leader's final read the
   PASID-cache ghost steps from the *evicted* cache to the *refilled* one:
   the ghost post-state is exactly
   `snd (vtd_device_translate_fill devtbl tbls contexts rid pasid
        (pasid_cache_evict cache ddid) mem iova)`,
   justified at the pure level by `vtd_device_translate_fill_after_evict`
   (the faithful instance has `ddid = d.(VtdDeviceEntry_did)` for the DTE `d`
   that `vtd_device_lookup devtbl rid` selects).  The ghost `dc_ctx` is a
   fresh `ghost_var` over `list PasidCacheEntry` — the device-table view of
   the cache the IOMMU will translate through is itself part of the verified
   state.

   As in `pasid_translate_weak.v`, the lift reuses
   `iommu_broadcast_full_gen_inv_update` (the generic R ⊢ |==> R' composition
   from S4.2b-2) with R / R' instantiated to the device-cache ghost;
   `vtd_device_dc_machine` threads it alongside the machine ghost, so the
   post-state carries both the IOTLB queue shootdown and the refilled
   device-table-keyed PASID cache. *)

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
Require Import machine_types.          (* Machine, VtdDeviceEntry, VtdPasid, PasidCacheEntry *)
Require Import machine.                (* vtd_device_translate_fill, pasid_cache_evict *)
Require Import shootdown_weak_broadcast. (* machine_ctx, bcG, machine_ctx_update, UTok, uniqTokG *)
Require Import iommu_proofs.           (* iommu_shootdown_via_queue *)
Require Import iommu_broadcast_weak.   (* iommu_broadcast, iommu_broadcast_full_gen_inv_update *)
Require Import iris.prelude.options.

(* ============================================================
   Ghost state: the device-table view of the PASID cache.  The machine ghost
   (bcG / machine_ctx) comes from shootdown_weak_broadcast; `dc_ctx` is a
   fresh ghost_var over the IOMMU's PASID cache, keyed (by the fill-on-miss
   loop) under the DTE's DID, so the leader can step it from the evicted
   cache to the refilled one at the final read.
   ============================================================ *)

Class dcG Σ := DcG { dc_cacheG : ghost_varG Σ (list PasidCacheEntry); }.
Local Existing Instances dc_cacheG.
Definition dcΣ : gFunctors := #[ghost_varΣ (list PasidCacheEntry)].
Global Instance subG_dcΣ {Σ} : subG dcΣ Σ → dcG Σ.
Proof. solve_inG. Qed.

(* The device-cache ghost, embedded into gpfsl's vProp. *)
Definition dc_ctx `{!dcG Σ} (γc : gname) (c : list PasidCacheEntry) : vProp Σ :=
  ⎡ ghost_var γc (DfracOwn 1) c ⎤.

#[global] Instance dc_ctx_objective `{!dcG Σ} γc c : Objective (dc_ctx γc c).
Proof. rewrite /dc_ctx. apply _. Qed.

(* The leader owns the cache ghost exclusively, so it may step it to any
   value; faithfulness (the ghost always matches the constrained physical
   cache) is by construction of the proof, exactly as in S2.1's Honesty note
   and S4.2b-2's machine corollary. *)
Lemma dc_ctx_update `{!dcG Σ} (γc : gname) (c c' : list PasidCacheEntry) :
  dc_ctx γc c ⊢ |==> dc_ctx γc c' : vProp Σ.
Proof.
  rewrite /dc_ctx. iIntros "Hc".
  iMod (ghost_var_update c' γc c with "Hc") as "Hc'".
  iIntros "!>". by iFrame.
Qed.

(* ============================================================
   The lift: the same two release/acquire pairs as S4.2b-2's `iommu_broadcast`
   (the invalidation doorbell and the completion), with R / R' instantiated
   to the device-cache ghost.  The pre-state is the cache *evicted by the
   DTE's DID* (the IOMMU is translating right after the device-selective
   invalidation) and the post-state is the *refilled* cache — the
   device-table fill-on-miss loop's cache result.
   ============================================================ *)

Lemma vtd_device_translate_dc_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !dcG Σ}
    (γc : gname) (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid ddid : Z) (cache : list PasidCacheEntry)
    (mem : list MemEntry) (iova : mword 64) :
  ∀ tid, {{{ dc_ctx γc (pasid_cache_evict cache ddid) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ dc_ctx γc (snd (vtd_device_translate_fill devtbl tbls contexts rid pasid
                                            (pasid_cache_evict cache ddid) mem iova)) }}}.
Proof.
  iIntros (tid Φ) "Hc Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (dc_ctx γc (pasid_cache_evict cache ddid))
            (dc_ctx γc (snd (vtd_device_translate_fill devtbl tbls contexts rid pasid
                              (pasid_cache_evict cache ddid) mem iova))) _ tid
            with "Hc").
  - iIntros (v) "(Hv & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (dc_ctx_update γc (pasid_cache_evict cache ddid)
           (snd (vtd_device_translate_fill devtbl tbls contexts rid pasid
                 (pasid_cache_evict cache ddid) mem iova))).
Qed.

(* The combined update: both ghosts step together (the IOTLB queue shootdown
   and the device-table PASID-cache fill). *)
Lemma dc_machine_update `{!bcG Σ, !dcG Σ} (γm γc : gname) (m m' : Machine)
    (c c' : list PasidCacheEntry) :
  (machine_ctx γm m ∗ dc_ctx γc c) ⊢ |==> (machine_ctx γm m' ∗ dc_ctx γc c') : vProp Σ.
Proof.
  iIntros "[Hm Hc]".
  iMod (machine_ctx_update γm m m' with "Hm") as "Hm'".
  iMod (dc_ctx_update γc c c' with "Hc") as "Hc'".
  iIntros "!>". iFrame.
Qed.

(* The machine-aware composition: the leader owns both ghosts exclusively and
   advances them — the machine to the functional queue-shootdown state and the
   device-table PASID cache to the fill-on-miss refill — while the final read
   is still the program's step (inside the WP), not in a postcondition
   adapter. *)
Lemma vtd_device_translate_dc_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !dcG Σ}
    (γm γc : gname) (m : Machine) (root : mword 44) (va : mword 64) (p : Pte)
    (devtbl : list VtdDeviceEntry) (tbls : list (list VtdPasid))
    (contexts : list VtdContext) (rid pasid ddid : Z) (cache : list PasidCacheEntry)
    (mem : list MemEntry) (iova : mword 64) :
  ∀ tid, {{{ machine_ctx γm m ∗ dc_ctx γc (pasid_cache_evict cache ddid) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm (iommu_shootdown_via_queue m root va p)
                    ∗ dc_ctx γc (snd (vtd_device_translate_fill devtbl tbls contexts rid pasid
                                        (pasid_cache_evict cache ddid) mem iova)) }}}.
Proof.
  iIntros (tid Φ) "Hm Post".
  iDestruct "Hm" as "[Hm Hc]".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ dc_ctx γc (pasid_cache_evict cache ddid))
            (machine_ctx γm (iommu_shootdown_via_queue m root va p)
             ∗ dc_ctx γc (snd (vtd_device_translate_fill devtbl tbls contexts rid pasid
                                 (pasid_cache_evict cache ddid) mem iova))) _ tid
            with "[$Hm $Hc]").
  - iIntros (v) "(Hv & Hm' & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (dc_machine_update γm γc m (iommu_shootdown_via_queue m root va p)
           (pasid_cache_evict cache ddid)
           (snd (vtd_device_translate_fill devtbl tbls contexts rid pasid
                 (pasid_cache_evict cache ddid) mem iova))).
Qed.

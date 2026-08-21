(* Tessera — SSG-4 / S4.5: the PASID gpfsl lift — the weak-memory (gpfsl)
   program over the in-loop PASID translation.

   The functional fill-on-miss loop (`pasid_translate_fill`, machine.sail,
   proved in vtd_proofs.v) is the S4.2b-1-style base: after an eviction the
   *loop* recovers — it re-walks the PASID table, refills the cache under the
   full (DID, PASID) tag, and answers with the table result
   (`pasid_translate_fill_after_evict`), leaving a coherent cache
   (`pasid_translate_fill_after_evict_refilled_coherent`).

   This file lifts that loop to genuine weak memory.  The leader (kernel /
   IOMMU driver) RELEASES the invalidation doorbell and the IOMMU ACQUIREs it
   before reading the request — the same release/acquire ordering core as
   S4.2b-2's `iommu_broadcast` — and at the leader's final read the
   PASID-cache ghost steps from the *evicted* cache to the *refilled* cache:
   the ghost post-state is exactly
   `snd (pasid_translate_fill … (pasid_cache_evict cache rid) …)`, justified
   at the pure level by the fill-on-miss lemmas.  This is the S4.5 analogue of
   `iommu_broadcast_full_gen_inv_machine` (the machine ghost) over a fresh
   `pc_ctx` ghost — `ghost_var` over `list PasidCacheEntry` — so the cache
   the IOMMU will translate through is itself part of the verified state.

   The lift reuses `iommu_broadcast_full_gen_inv_update` (the generic
   R ⊢ |==> R' composition from S4.2b-2) with R / R' instantiated to the
   PASID-cache ghost; `pasid_translate_pc_machine` threads it alongside the
   machine ghost, so the post-state carries both the IOTLB queue shootdown
   and the refilled PASID cache. *)

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
Require Import machine_types.          (* Machine, Pte, VtdContext, VtdPasid, PasidCacheEntry *)
Require Import machine.                (* pasid_translate_fill, pasid_cache_evict *)
Require Import shootdown_weak_broadcast. (* machine_ctx, bcG, machine_ctx_update, UTok, uniqTokG *)
Require Import iommu_proofs.           (* iommu_shootdown_via_queue *)
Require Import iommu_broadcast_weak.   (* iommu_broadcast, iommu_broadcast_full_gen_inv_update *)
Require Import iris.prelude.options.

(* ============================================================
   Ghost state: only the PASID-cache ghost.  The machine ghost (bcG /
   machine_ctx) comes from shootdown_weak_broadcast; `pc_ctx` is a fresh
   ghost_var over the IOMMU's PASID cache, so the leader can step it from the
   evicted cache to the refilled one at the final read.
   ============================================================ *)

Class pcG Σ := PcG { pc_cacheG : ghost_varG Σ (list PasidCacheEntry); }.
Local Existing Instances pc_cacheG.
Definition pcΣ : gFunctors := #[ghost_varΣ (list PasidCacheEntry)].
Global Instance subG_pcΣ {Σ} : subG pcΣ Σ → pcG Σ.
Proof. solve_inG. Qed.

(* The PASID-cache ghost, embedded into gpfsl's vProp. *)
Definition pc_ctx `{!pcG Σ} (γc : gname) (c : list PasidCacheEntry) : vProp Σ :=
  ⎡ ghost_var γc (DfracOwn 1) c ⎤.

#[global] Instance pc_ctx_objective `{!pcG Σ} γc c : Objective (pc_ctx γc c).
Proof. rewrite /pc_ctx. apply _. Qed.

(* The leader owns the cache ghost exclusively, so it may step it to any
   value; faithfulness (the ghost always matches the constrained physical
   cache) is by construction of the proof, exactly as in S2.1's Honesty note
   and S4.2b-2's machine corollary. *)
Lemma pc_ctx_update `{!pcG Σ} (γc : gname) (c c' : list PasidCacheEntry) :
  pc_ctx γc c ⊢ |==> pc_ctx γc c' : vProp Σ.
Proof.
  rewrite /pc_ctx. iIntros "Hc".
  iMod (ghost_var_update c' γc c with "Hc") as "Hc'".
  iIntros "!>". by iFrame.
Qed.

(* ============================================================
   The lift: the same two release/acquire pairs as S4.2b-2's `iommu_broadcast`
   (the invalidation doorbell and the completion), with R / R' instantiated
   to the PASID-cache ghost.  The pre-state is the *evicted* cache (the IOMMU
   is translating right after the device-selective invalidation) and the
   post-state is the *refilled* cache — the fill-on-miss loop's cache result.
   ============================================================ *)

Lemma pasid_translate_pc_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !pcG Σ}
    (γc : gname) (contexts : list VtdContext) (rid pasid : Z) (ptes : list VtdPasid)
    (cache : list PasidCacheEntry) (mem : list MemEntry) (iova : mword 64) :
  ∀ tid, {{{ pc_ctx γc (pasid_cache_evict cache rid) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ pc_ctx γc (snd (pasid_translate_fill contexts rid ptes
                                            (pasid_cache_evict cache rid) pasid mem iova)) }}}.
Proof.
  iIntros (tid Φ) "Hc Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (pc_ctx γc (pasid_cache_evict cache rid))
            (pc_ctx γc (snd (pasid_translate_fill contexts rid ptes
                              (pasid_cache_evict cache rid) pasid mem iova))) _ tid
            with "Hc").
  - iIntros (v) "(Hv & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (pc_ctx_update γc (pasid_cache_evict cache rid)
           (snd (pasid_translate_fill contexts rid ptes (pasid_cache_evict cache rid) pasid mem iova))).
Qed.

(* The combined update: both ghosts step together (the IOTLB queue shootdown
   and the PASID-cache fill). *)
Lemma pc_machine_update `{!bcG Σ, !pcG Σ} (γm γc : gname) (m m' : Machine)
    (c c' : list PasidCacheEntry) :
  (machine_ctx γm m ∗ pc_ctx γc c) ⊢ |==> (machine_ctx γm m' ∗ pc_ctx γc c') : vProp Σ.
Proof.
  iIntros "[Hm Hc]".
  iMod (machine_ctx_update γm m m' with "Hm") as "Hm'".
  iMod (pc_ctx_update γc c c' with "Hc") as "Hc'".
  iIntros "!>". iFrame.
Qed.

(* The machine-aware composition: the leader owns both ghosts exclusively and
   advances them — the machine to the functional queue-shootdown state and the
   PASID cache to the fill-on-miss refill — while the final read is still the
   program's step (inside the WP), not in a postcondition adapter. *)
Lemma pasid_translate_pc_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !pcG Σ}
    (γm γc : gname) (m : Machine) (root : mword 44) (va : mword 64) (p : Pte)
    (contexts : list VtdContext) (rid pasid : Z) (ptes : list VtdPasid)
    (cache : list PasidCacheEntry) (mem : list MemEntry) (iova : mword 64) :
  ∀ tid, {{{ machine_ctx γm m ∗ pc_ctx γc (pasid_cache_evict cache rid) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm (iommu_shootdown_via_queue m root va p)
                    ∗ pc_ctx γc (snd (pasid_translate_fill contexts rid ptes
                                        (pasid_cache_evict cache rid) pasid mem iova)) }}}.
Proof.
  iIntros (tid Φ) "Hm Post".
  iDestruct "Hm" as "[Hm Hc]".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ pc_ctx γc (pasid_cache_evict cache rid))
            (machine_ctx γm (iommu_shootdown_via_queue m root va p)
             ∗ pc_ctx γc (snd (pasid_translate_fill contexts rid ptes
                                 (pasid_cache_evict cache rid) pasid mem iova))) _ tid
            with "[$Hm $Hc]").
  - iIntros (v) "(Hv & Hm' & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (pc_machine_update γm γc m (iommu_shootdown_via_queue m root va p)
           (pasid_cache_evict cache rid)
           (snd (pasid_translate_fill contexts rid ptes (pasid_cache_evict cache rid) pasid mem iova))).
Qed.

(* ============================================================
   S4.5 gen-tag lift: the generation-tagged PASID fill-on-miss loop
   (`pasid_translate_fill_gen`) as a weak program.  The pre-state is the
   stale-tag eviction state and the post-state is the cache returned by the
   gen-g fill loop.  The epoch is Tessera's address-space-reuse tag; the
   release/acquire protocol is the same IOMMU broadcast protocol used by the
   generation-0 lift above.
   ============================================================ *)

Lemma pasid_translate_gen_pc_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !pcG Σ}
    (γc : gname) (contexts : list VtdContext) (rid pasid g : Z)
    (ptes : list VtdPasid) (cache : list PasidCacheEntry)
    (mem : list MemEntry) (iova : mword 64) :
  ∀ tid, {{{ pc_ctx γc (pasid_cache_evict_gen cache (rid, pasid) g) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ pc_ctx γc (snd (pasid_translate_fill_gen contexts rid ptes
                                      (pasid_cache_evict_gen cache (rid, pasid) g)
                                      pasid mem iova g)) }}}.
Proof.
  iIntros (tid Φ) "Hc Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (pc_ctx γc (pasid_cache_evict_gen cache (rid, pasid) g))
            (pc_ctx γc (snd (pasid_translate_fill_gen contexts rid ptes
                                      (pasid_cache_evict_gen cache (rid, pasid) g)
                                      pasid mem iova g))) _ tid
            with "Hc").
  - iIntros (v) "(Hv & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (pc_ctx_update γc (pasid_cache_evict_gen cache (rid, pasid) g)
           (snd (pasid_translate_fill_gen contexts rid ptes
                 (pasid_cache_evict_gen cache (rid, pasid) g) pasid mem iova g))).
Qed.
Lemma pasid_translate_gen_pc_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !pcG Σ}
    (γm γc : gname) (m : Machine) (root : mword 44) (va : mword 64) (p : Pte)
    (contexts : list VtdContext) (rid pasid g : Z) (ptes : list VtdPasid)
    (cache : list PasidCacheEntry) (mem : list MemEntry) (iova : mword 64) :
  ∀ tid, {{{ machine_ctx γm m ∗ pc_ctx γc (pasid_cache_evict_gen cache (rid, pasid) g) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm (iommu_shootdown_via_queue m root va p)
                    ∗ pc_ctx γc (snd (pasid_translate_fill_gen contexts rid ptes
                                      (pasid_cache_evict_gen cache (rid, pasid) g)
                                      pasid mem iova g)) }}}.
Proof.
  iIntros (tid Φ) "[Hm Hc] Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ pc_ctx γc (pasid_cache_evict_gen cache (rid, pasid) g))
            (machine_ctx γm (iommu_shootdown_via_queue m root va p)
             ∗ pc_ctx γc (snd (pasid_translate_fill_gen contexts rid ptes
                                      (pasid_cache_evict_gen cache (rid, pasid) g)
                                      pasid mem iova g))) _ tid
            with "[$Hm $Hc]").
  - iIntros (v) "(Hv & Hm' & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (pc_machine_update γm γc m (iommu_shootdown_via_queue m root va p)
           (pasid_cache_evict_gen cache (rid, pasid) g)
           (snd (pasid_translate_fill_gen contexts rid ptes
                 (pasid_cache_evict_gen cache (rid, pasid) g) pasid mem iova g))).
Qed.

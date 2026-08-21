(* Tessera — SSG-4 / S4.5: the AMD-Vi walker's IOTLB gpfsl lift — the
   weak-memory (gpfsl) program over the AMD-Vi fill-on-miss translation loop.

   The functional base is `amdvi_translate_fill` (machine.sail, proved in
   amdvi_proofs.v): the AMD-Vi translation service loop consults its IOTLB
   (keyed by (DID = 0, IOVA); the IOMMU is legacy domain 0 for a device
   without PASID SVM) before the four-level walk.  A hit answers from the
   cache without touching the page tables; a miss re-walks and refills the
   IOTLB under (0, iova); after a 4KiB INVALIDATE_IOMMU_PAGES of the page no
   cached entry survives (`iotlb_lookup_after_invalidate`), so the loop
   re-walks and recovers — the invalidate-then-retranslate cycle
   (`amdvi_translate_fill_after_invalidate`).

   This file lifts that loop to genuine weak memory, exactly as
   `smmu_translate_weak.v` / `pasid_translate_weak.v` /
   `vtd_device_translate_weak.v` lift the SMMU/VT-d cache loops: the leader
   (kernel / AMD-Vi driver) RELEASES the invalidation doorbell and the IOMMU
   ACQUIREs it before serving the request — the same release/acquire ordering
   core as S4.2b-2's `iommu_broadcast` — and at the leader's final read the
   IOTLB ghost steps from the *invalidated* cache to the *refilled* one: the
   ghost post-state is exactly
   `snd (amdvi_translate_fill root (iotlb_invalidate iotlb iova) mem iova)`,
   justified at the pure level by `amdvi_translate_fill_after_invalidate`.
   The ghost `ag_ctx` is a fresh `ghost_var` over `list IotlbEntry` — the
   AMD-Vi IOTLB, the device-side twin of the VT-d device-table PASID cache.

   As in the cache lifts, the lift reuses
   `iommu_broadcast_full_gen_inv_update` (the generic R ⊢ |==> R' composition
   from S4.2b-2) with R / R' instantiated to the IOTLB ghost;
   `amdvi_translate_ag_machine` threads it alongside the machine ghost, so the
   post-state carries both the IOTLB queue shootdown and the refilled AMD-Vi
   IOTLB. *)

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
Require Import machine_types.          (* Machine, IotlbEntry *)
Require Import machine.                (* amdvi_translate_fill, iotlb_invalidate *)
Require Import shootdown_weak_broadcast. (* machine_ctx, bcG, machine_ctx_update, UTok, uniqTokG *)
Require Import iommu_proofs.           (* iommu_shootdown_via_queue *)
Require Import iommu_broadcast_weak.   (* iommu_broadcast, iommu_broadcast_full_gen_inv_update *)
Require Import iris.prelude.options.

(* ============================================================
   Ghost state: the AMD-Vi IOTLB.  The machine ghost (bcG / machine_ctx)
   comes from shootdown_weak_broadcast; `ag_ctx` is a fresh ghost_var over
   the AMD-Vi translation cache, stepped at the leader's final read from the
   invalidated cache to the refilled one.
   ============================================================ *)

Class agG Σ := AgG { ag_iotlbG : ghost_varG Σ (list IotlbEntry); }.
Local Existing Instances ag_iotlbG.
Definition agΣ : gFunctors := #[ghost_varΣ (list IotlbEntry)].
Global Instance subG_agΣ {Σ} : subG agΣ Σ → agG Σ.
Proof. solve_inG. Qed.

(* The AMD-Vi-IOTLB ghost, embedded into gpfsl's vProp. *)
Definition ag_ctx `{!agG Σ} (γi : gname) (iotlb : list IotlbEntry) : vProp Σ :=
  ⎡ ghost_var γi (DfracOwn 1) iotlb ⎤.

#[global] Instance ag_ctx_objective `{!agG Σ} γi iotlb : Objective (ag_ctx γi iotlb).
Proof. rewrite /ag_ctx. apply _. Qed.

(* The leader owns the IOTLB ghost exclusively, so it may step it to any
   value; faithfulness (the ghost always matches the constrained physical
   cache) is by construction of the proof, exactly as in S2.1's Honesty note
   and the S4.2b-2 machine corollary. *)
Lemma ag_ctx_update `{!agG Σ} (γi : gname) (c c' : list IotlbEntry) :
  ag_ctx γi c ⊢ |==> ag_ctx γi c' : vProp Σ.
Proof.
  rewrite /ag_ctx. iIntros "Hc".
  iMod (ghost_var_update c' γi c with "Hc") as "Hc'".
  iIntros "!>". by iFrame.
Qed.

(* ============================================================
   The lift: the same two release/acquire pairs as S4.2b-2's `iommu_broadcast`
   (the invalidation doorbell and the completion), with R / R' instantiated
   to the AMD-Vi-IOTLB ghost.  The pre-state is the cache *after a 4KiB
   INVALIDATE_IOMMU_PAGES of the page* (the IOTLB is empty of the page's
   entries) and the post-state is the *refilled* cache — the fill-on-miss
   loop's cache result.
   ============================================================ *)

Lemma amdvi_translate_ag_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !agG Σ}
    (γi : gname) (root : mword 44)
    (iotlb : list IotlbEntry) (mem : list MemEntry) (iova : mword 64) :
  ∀ tid, {{{ ag_ctx γi (iotlb_invalidate iotlb iova) } }}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ ag_ctx γi (snd (amdvi_translate_fill root
                                        (iotlb_invalidate iotlb iova) mem iova)) }}}.
Proof.
  iIntros (tid Φ) "Hc Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (ag_ctx γi (iotlb_invalidate iotlb iova))
            (ag_ctx γi (snd (amdvi_translate_fill root
                              (iotlb_invalidate iotlb iova) mem iova))) _ tid
            with "Hc").
  - iIntros (v) "(Hv & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (ag_ctx_update γi (iotlb_invalidate iotlb iova)
           (snd (amdvi_translate_fill root
                 (iotlb_invalidate iotlb iova) mem iova))).
Qed.

(* The combined update: both ghosts step together (the IOTLB queue shootdown
   and the AMD-Vi-IOTLB refill). *)
Lemma ag_machine_update `{!bcG Σ, !agG Σ} (γm γi : gname) (m m' : Machine)
    (c c' : list IotlbEntry) :
  (machine_ctx γm m ∗ ag_ctx γi c) ⊢ |==> (machine_ctx γm m' ∗ ag_ctx γi c') : vProp Σ.
Proof.
  iIntros "[Hm Hc]".
  iMod (machine_ctx_update γm m m' with "Hm") as "Hm'".
  iMod (ag_ctx_update γi c c' with "Hc") as "Hc'".
  iIntros "!>". iFrame.
Qed.

(* The machine-aware composition: the leader owns both ghosts exclusively and
   advances them — the machine to the functional queue-shootdown state and the
   AMD-Vi IOTLB to the fill-on-miss refill — while the final read is still the
   program's step (inside the WP), not in a postcondition adapter. *)
Lemma amdvi_translate_ag_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !agG Σ}
    (γm γi : gname) (m : Machine) (root : mword 44) (va : mword 64) (p : Pte)
    (iotlb : list IotlbEntry) (mem : list MemEntry) (iova : mword 64) :
  ∀ tid, {{{ machine_ctx γm m ∗ ag_ctx γi (iotlb_invalidate iotlb iova) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm (iommu_shootdown_via_queue m root va p)
                    ∗ ag_ctx γi (snd (amdvi_translate_fill root
                                      (iotlb_invalidate iotlb iova) mem iova)) }}}.
Proof.
  iIntros (tid Φ) "Hm Post".
  iDestruct "Hm" as "[Hm Hc]".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ ag_ctx γi (iotlb_invalidate iotlb iova))
            (machine_ctx γm (iommu_shootdown_via_queue m root va p)
             ∗ ag_ctx γi (snd (amdvi_translate_fill root
                               (iotlb_invalidate iotlb iova) mem iova))) _ tid
            with "[$Hm $Hc]").
  - iIntros (v) "(Hv & Hm' & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (ag_machine_update γm γi m (iommu_shootdown_via_queue m root va p)
           (iotlb_invalidate iotlb iova)
           (snd (amdvi_translate_fill root
                 (iotlb_invalidate iotlb iova) mem iova))).
Qed.

(* Tessera — SSG-4 / S4.5: the SMMU walker's IOTLB gpfsl lift — the
   weak-memory (gpfsl) program over the SMMU's fill-on-miss translation loop.

   The functional base is `smmu_translate_fill` (machine.sail, proved in
   smmu_proofs.v): the SMMU's translation service loop consults its IOTLB
   (keyed by (SID, VA); the ASID is the pasid tag, 0 without SVM) before the
   STE -> CD -> stage-1/stage-2 walk.  A hit answers from the cache without
   touching the page tables; a miss re-walks and refills the IOTLB under
   (sid, gva); after a 4KiB TLBI of the page no cached entry survives
   (`iotlb_lookup_after_invalidate`), so the loop re-walks and recovers —
   the invalidate-then-retranslate cycle (`smmu_translate_fill_after_invalidate`).

   This file lifts that loop to genuine weak memory, exactly as
   `pasid_translate_weak.v` / `vtd_device_translate_weak.v` lift the VT-d
   cache loops: the leader (kernel / SMMU driver) RELEASES the invalidation
   doorbell and the SMMU ACQUIREs it before serving the request — the same
   release/acquire ordering core as S4.2b-2's `iommu_broadcast` — and at the
   leader's final read the IOTLB ghost steps from the *invalidated* cache to
   the *refilled* one: the ghost post-state is exactly
   `snd (smmu_translate_fill stes cds sid (iotlb_invalidate iotlb gva) mem gva)`,
   justified at the pure level by `smmu_translate_fill_after_invalidate`.
   The ghost `sg_ctx` is a fresh `ghost_var` over `list IotlbEntry` — the
   SMMU's IOTLB, the device-side twin of the VT-d device-table PASID cache.

   As in the cache lifts, the lift reuses
   `iommu_broadcast_full_gen_inv_update` (the generic R ⊢ |==> R' composition
   from S4.2b-2) with R / R' instantiated to the IOTLB ghost;
   `smmu_translate_sg_machine` threads it alongside the machine ghost, so the
   post-state carries both the IOTLB queue shootdown and the refilled SMMU
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
Require Import machine_types.          (* Machine, Ste, Cd, IotlbEntry *)
Require Import machine.                (* smmu_translate_fill, iotlb_invalidate *)
Require Import shootdown_weak_broadcast. (* machine_ctx, bcG, machine_ctx_update, UTok, uniqTokG *)
Require Import iommu_proofs.           (* iommu_shootdown_via_queue *)
Require Import iommu_broadcast_weak.   (* iommu_broadcast, iommu_broadcast_full_gen_inv_update *)
Require Import iris.prelude.options.

(* ============================================================
   Ghost state: the SMMU's IOTLB.  The machine ghost (bcG / machine_ctx)
   comes from shootdown_weak_broadcast; `sg_ctx` is a fresh ghost_var over
   the SMMU's translation cache, stepped at the leader's final read from the
   invalidated cache to the refilled one.
   ============================================================ *)

Class sgG Σ := SgG { sg_iotlbG : ghost_varG Σ (list IotlbEntry); }.
Local Existing Instances sg_iotlbG.
Definition sgΣ : gFunctors := #[ghost_varΣ (list IotlbEntry)].
Global Instance subG_sgΣ {Σ} : subG sgΣ Σ → sgG Σ.
Proof. solve_inG. Qed.

(* The SMMU-IOTLB ghost, embedded into gpfsl's vProp. *)
Definition sg_ctx `{!sgG Σ} (γi : gname) (iotlb : list IotlbEntry) : vProp Σ :=
  ⎡ ghost_var γi (DfracOwn 1) iotlb ⎤.

#[global] Instance sg_ctx_objective `{!sgG Σ} γi iotlb : Objective (sg_ctx γi iotlb).
Proof. rewrite /sg_ctx. apply _. Qed.

(* The leader owns the IOTLB ghost exclusively, so it may step it to any
   value; faithfulness (the ghost always matches the constrained physical
   cache) is by construction of the proof, exactly as in S2.1's Honesty note
   and the S4.2b-2 machine corollary. *)
Lemma sg_ctx_update `{!sgG Σ} (γi : gname) (c c' : list IotlbEntry) :
  sg_ctx γi c ⊢ |==> sg_ctx γi c' : vProp Σ.
Proof.
  rewrite /sg_ctx. iIntros "Hc".
  iMod (ghost_var_update c' γi c with "Hc") as "Hc'".
  iIntros "!>". by iFrame.
Qed.

(* ============================================================
   The lift: the same two release/acquire pairs as S4.2b-2's `iommu_broadcast`
   (the invalidation doorbell and the completion), with R / R' instantiated
   to the SMMU-IOTLB ghost.  The pre-state is the cache *after a 4KiB TLBI of
   the page* (the IOTLB is empty of the page's entries) and the post-state is
   the *refilled* cache — the fill-on-miss loop's cache result.
   ============================================================ *)

Lemma smmu_translate_sg_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !sgG Σ}
    (γi : gname) (stes : list Ste) (cds : list Cd) (sid : Z)
    (iotlb : list IotlbEntry) (mem : list MemEntry) (gva : mword 64) :
  ∀ tid, {{{ sg_ctx γi (iotlb_invalidate iotlb gva) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ sg_ctx γi (snd (smmu_translate_fill stes cds sid
                                        (iotlb_invalidate iotlb gva) mem gva)) }}}.
Proof.
  iIntros (tid Φ) "Hc Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (sg_ctx γi (iotlb_invalidate iotlb gva))
            (sg_ctx γi (snd (smmu_translate_fill stes cds sid
                              (iotlb_invalidate iotlb gva) mem gva))) _ tid
            with "Hc").
  - iIntros (v) "(Hv & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (sg_ctx_update γi (iotlb_invalidate iotlb gva)
           (snd (smmu_translate_fill stes cds sid
                 (iotlb_invalidate iotlb gva) mem gva))).
Qed.

(* The combined update: both ghosts step together (the IOTLB queue shootdown
   and the SMMU-IOTLB refill). *)
Lemma sg_machine_update `{!bcG Σ, !sgG Σ} (γm γi : gname) (m m' : Machine)
    (c c' : list IotlbEntry) :
  (machine_ctx γm m ∗ sg_ctx γi c) ⊢ |==> (machine_ctx γm m' ∗ sg_ctx γi c') : vProp Σ.
Proof.
  iIntros "[Hm Hc]".
  iMod (machine_ctx_update γm m m' with "Hm") as "Hm'".
  iMod (sg_ctx_update γi c c' with "Hc") as "Hc'".
  iIntros "!>". iFrame.
Qed.

(* The machine-aware composition: the leader owns both ghosts exclusively and
   advances them — the machine to the functional queue-shootdown state and the
   SMMU IOTLB to the fill-on-miss refill — while the final read is still the
   program's step (inside the WP), not in a postcondition adapter. *)
Lemma smmu_translate_sg_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !sgG Σ}
    (γm γi : gname) (m : Machine) (root : mword 44) (va : mword 64) (p : Pte)
    (stes : list Ste) (cds : list Cd) (sid : Z)
    (iotlb : list IotlbEntry) (mem : list MemEntry) (gva : mword 64) :
  ∀ tid, {{{ machine_ctx γm m ∗ sg_ctx γi (iotlb_invalidate iotlb gva) }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm (iommu_shootdown_via_queue m root va p)
                    ∗ sg_ctx γi (snd (smmu_translate_fill stes cds sid
                                      (iotlb_invalidate iotlb gva) mem gva)) }}}.
Proof.
  iIntros (tid Φ) "Hm Post".
  iDestruct "Hm" as "[Hm Hc]".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ sg_ctx γi (iotlb_invalidate iotlb gva))
            (machine_ctx γm (iommu_shootdown_via_queue m root va p)
             ∗ sg_ctx γi (snd (smmu_translate_fill stes cds sid
                               (iotlb_invalidate iotlb gva) mem gva))) _ tid
            with "[$Hm $Hc]").
  - iIntros (v) "(Hv & Hm' & Hc')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hc'". iPureIntro. exact Hv.
  Unshelve.
  exact (sg_machine_update γm γi m (iommu_shootdown_via_queue m root va p)
           (iotlb_invalidate iotlb gva)
           (snd (smmu_translate_fill stes cds sid
                 (iotlb_invalidate iotlb gva) mem gva))).
Qed.

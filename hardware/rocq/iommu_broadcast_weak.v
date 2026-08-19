(* Tessera — SSG-4 / S4.2b-2: the IOMMU broadcast's weak-memory ordering core,
   two parties (leader + IOMMU), first direction (leader → IOMMU).

   S4.2a/S4.2b-1 proved the *functional* IOMMU broadcast: unmap → enqueue
   Invalidate+Wait → drain ⇒ the IOTLB is invalidated
   (`iommu_shootdown_via_queue_correct`).  S4.2b-2 lifts that to genuine weak
   memory: the leader's PTE write + doorbell (release) must be observed by the
   IOMMU's queue read (acquire) before the drain completes, and the IOMMU's
   Invalidation-Wait completion (release) must be observed by the leader's
   completion read (acquire).

   This file proves the *first* direction — the leader → IOMMU doorbell: the
   leader RELEASES the doorbell (cell 0), and the IOMMU ACQUIRE-spins on it and
   then reads the request cell (cell 1), provably observing the leader's
   invalidate request.  It is a faithful re-instantiation of S2.2a's
   `shootdown_weak_gen_inv` (the leader → remote PTE-invalidation ordering) with
   the message `encode_pte invalid_pte` replaced by the flag `1` (the unmap
   request) and the cells renamed door/req.  The token algebra (`UTok`,
   `uniqTokΣ`) is reused verbatim from shootdown_weak.v.

   The second direction (IOMMU → leader Invalidation-Wait completion) and the
   composition into `iommu_broadcast_spec` are the next increments (see
   doc/iommu-shootdown-plan.md, S4.2b-2). *)

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import lifting proofmode atomics view_invariants
                                 repeat_loop new_delete.
From iris.algebra Require Import excl.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Import proofmode monpred.
From gpfsl.base_logic Require Import vprop.
From SailStdpp Require Import MachineWord.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import shootdown_weak.  (* UTok, uniqTokΣ, subG_uniqTokΣ, UTok_alloc, UTok_unique *)
Require Import iris.prelude.options.

(* ===== the program: the IOMMU ordering core, leader -> IOMMU =====
   cell 0 = door (the doorbell); cell 1 = req (the invalidate request). *)

Abbreviation door := 0%Z.
Abbreviation req := 1%Z.

Definition iommu_broadcast_weak : expr :=
  let: "m" := new [ #2] in
  "m" +ₗ #door <- #0 ;;
  "m" +ₗ #req <- #0 ;;
  Fork ("m" +ₗ #req <- #1 ;;          (* leader: the unmap/invalidate request *)
        "m" +ₗ #door <-ʳᵉˡ #1) ;;     (* release: the doorbell *)
  (repeat: !ᵃᶜ("m" +ₗ #door)) ;;      (* IOMMU: acquire the doorbell *)
  !("m" +ₗ #req).                      (* IOMMU: read — provably the request *)

Definition iommu_broadcast_spec Σ `{!noprolG Σ} (e : expr) :=
  ∀ tid, {{{ True }}} e @ tid; ⊤ {{{ v, RET #v; ⌜v = 1⌝ }}}.

Definition iqN (n : loc) := nroot .@ "iqN" .@ n.

(* ===== invariant + proof (gpfsl mp proof_gen_inv, the request as the message) ===== *)
Implicit Types (x : loc) (γ : gname) (ζ : absHist) (t : time) (V : view).

Section inv.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.
#[local] Abbreviation vProp := (vProp Σ).

Definition iq_inv'_def (x y : loc) γ γx : vProp :=
  (∃ ζ (b : bool) t0 V0 Vx,
    @{Vx} (x sw↦{γx} ζ) ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
              (UTok γ ∨ @{V1} (y ↦ #1))
    end
  )%I.
Definition iq_inv'_aux : seal (@iq_inv'_def). Proof. by eexists. Qed.
Definition iq_inv' := unseal (@iq_inv'_aux).
Definition iq_inv'_eq : @iq_inv' = _ := seal_eq _.

#[global] Instance iq_inv'_objective x y γ γx : Objective (iq_inv' x y γ γx).
Proof.
  rewrite iq_inv'_eq.
  apply exists_objective=>?. apply exists_objective=>[[|]]; by apply _.
Qed.

Definition iq_inv N x y γ γx := inv N (iq_inv' x y γ γx).
End inv.

Lemma iommu_broadcast_gen_inv `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ} :
  iommu_broadcast_spec Σ iommu_broadcast_weak.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /iommu_broadcast_weak.
  (* allocation *)
  wp_apply wp_new; [done..|].
  iIntros (m) "(DEL & m & Hm)". rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "m" as "[m0 m1]".
  (* initializing *)
  wp_pures. rewrite shift_0. wp_write. wp_op. wp_write.

  (* constructing the invariant *)
  iMod UTok_alloc as (γ) "Tok".
  iMod (AtomicPtsTo_from_na with "m0") as (γx t V) "(#SeenV & SW & Pts)".
  iDestruct (AtomicSWriter_AtomicSync with "SW") as "#S".
  iDestruct (view_at_intro with "Pts") as (Vx) "[SeenVx Pts]".
  iMod (inv_alloc (iqN m) _ (iq_inv' ((m >> 0%nat)%stdpp) ((m >> 1%nat)%stdpp) γ γx)
          with "[Pts]") as "#Inv".
  { rewrite iq_inv'_eq. iIntros "!>".
    iExists _, false, t, V, Vx. rewrite shift_0. by iFrame "Pts". }
  (* forking *)
  wp_apply (wp_fork with "[SW m1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write. wp_op. rewrite shift_0.
    (* open shared invariant *)
    iInv (iqN m) as "INV" "Close". rewrite iq_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts _]".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Pts SW") as %->.
    (* actual write of flag *)
    iApply (AtomicSWriter_release_write _ _ _ _ V Vx0 #1
              (((m >> 1%nat)%stdpp) ↦{1} #1)%I
              with "[$SW $Pts $m1 $SeenV]"); [solve_ndisj|..].
    iIntros "!>" (t1 V1) "(%MAX & SeenV' & [m1 SW'] & Pts')".
    (* reestablishing the invariant *)
    iMod ("Close" with "[-]"); last done.
    iIntros "!>". iExists _, true, t, V, _. iFrame "Pts'".
    iExists t1, V1. iSplit.
    { iPureIntro. split; [|done]. apply MAX. rewrite lookup_insert_eq. by eexists. }
    iRight. by iFrame "m1".

  - iIntros "_". wp_seq. wp_bind (repeat: _)%E.
    (* repeat loop *)
    iLöb as "IH". iApply wp_repeat; [done|].
    wp_op. rewrite shift_0.

    (* open shared invariant *)
    iInv (iqN m) as "INV" "Close". rewrite iq_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts Own]".

    (* actual read *)
    iApply (AtomicSeen_acquire_read with "[$Pts $SeenV]"); [solve_ndisj|..].
    { by iApply (AtomicSync_AtomicSeen with "S"). }
    iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Pts)".
    iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & MAX'' & LeV'').

    case (decide (t' = t0)) => [?|NEqt'].
    + subst t'.
      (* must have read the flag to be 0 *)
      iAssert (⌜v' = #0⌝)%I as %Eq0.
      { destruct b.
        - iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "_".
          iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert_ne in Sub2.
          + rewrite lookup_insert_eq in Sub2. by inversion Sub2.
          + clear -Lt1. intros ?. subst. lia.
        - iDestruct "Own" as %Eqζ'. iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert_eq in Sub2. by inversion Sub2. }
      (* keep looping *)
      iMod ("Close" with "[Pts Own]").
      { iIntros "!>". iExists ζ', b, t0, V0, _. by iFrame. }
      iIntros "!>". iExists 0. iSplit; [done|].
      iIntros "!> !>". by iApply ("IH" with "Post DEL Hm Tok SeenVx").

    + destruct b; last first.
      { (* b cannot be false *)
        iDestruct "Own" as %Eqζ'. exfalso.
        rewrite Eqζ' in Sub2.
        apply (lookup_weaken _ _ _ _ Eqt'), lookup_singleton_Some in Sub2 as [].
        by apply NEqt'. }
      iClear "IH".
      (* read 1: extract the data via the released view *)
      iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "Own".
      rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      have ? : t' = t1.
      { case (decide (t' = t1)) => [//|NEqt1].
        exfalso. by rewrite !lookup_insert_ne // in Sub2. }
      subst t'. rewrite lookup_insert_eq in Sub2. inversion Sub2. subst v' V'.

      iDestruct "Own" as "[Own|Data]".
      { iExFalso. by iDestruct (UTok_unique with "Tok Own") as "$". }
      iDestruct (view_at_elim with "[SV'] Data") as "Data".
      { iApply (monPred_in_mono with "SV'"). simpl. solve_lat. }

      iMod ("Close" with "[Pts Tok]").
      { iIntros "!>". iExists ζ', true, t0, V0, _. iFrame "Pts".
        iExists t1, V1. iSplit; [done|]. by iLeft. }
      iIntros "!>". iExists 1. iSplit; [done|].
      iIntros "!> !>".

      wp_pures. wp_read. by iApply "Post".
Qed.

(* ============================================================
   S4.2b-2 (second direction) — the IOMMU -> leader completion.

   The leader released the doorbell (above); now the IOMMU, after acquiring
   that doorbell and draining the queue, RELEASES the Invalidation-Wait
   completion, and the leader ACQUIRE-spins on it and reads the result cell,
   provably observing the drained IOTLB.  This is `shootdown_weak_ack_gen_inv`
   (the remote -> leader ack round-trip) with `encode_tlb None` replaced by the
   flag `1` (the drain completion) and the cells renamed done/res.
   ============================================================ *)

Abbreviation done := 0%Z.
Abbreviation res := 1%Z.

Definition iommu_broadcast_ack : expr :=
  let: "m" := new [ #2] in
  "m" +ₗ #done <- #0 ;;
  "m" +ₗ #res <- #0 ;;
  Fork ("m" +ₗ #res <- #1 ;;            (* IOMMU: the drained IOTLB result *)
        "m" +ₗ #done <-ʳᵉˡ #1) ;;       (* release: the Invalidation-Wait completion *)
  (repeat: !ᵃᶜ("m" +ₗ #done)) ;;        (* leader: acquire the completion *)
  !("m" +ₗ #res).                       (* leader: read — provably the result *)

Definition iommu_broadcast_ack_spec Σ `{!noprolG Σ} (e : expr) :=
  ∀ tid, {{{ True }}} e @ tid; ⊤ {{{ v, RET #v; ⌜v = 1⌝ }}}.

Definition iqN_ack (n : loc) := nroot .@ "iqNack" .@ n.

Section inv_ack.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.
#[local] Abbreviation vProp := (vProp Σ).

Definition iq_ack_inv'_def (x y : loc) γ γx : vProp :=
  (∃ ζ (b : bool) t0 V0 Vx,
    @{Vx} (x sw↦{γx} ζ) ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
              (UTok γ ∨ @{V1} (y ↦ #1))
    end
  )%I.
Definition iq_ack_inv'_aux : seal (@iq_ack_inv'_def). Proof. by eexists. Qed.
Definition iq_ack_inv' := unseal (@iq_ack_inv'_aux).
Definition iq_ack_inv'_eq : @iq_ack_inv' = _ := seal_eq _.

#[global] Instance iq_ack_inv'_objective x y γ γx : Objective (iq_ack_inv' x y γ γx).
Proof.
  rewrite iq_ack_inv'_eq.
  apply exists_objective=>?. apply exists_objective=>[[|]]; by apply _.
Qed.

Definition iq_ack_inv N x y γ γx := inv N (iq_ack_inv' x y γ γx).
End inv_ack.

Lemma iommu_broadcast_ack_gen_inv `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ} :
  iommu_broadcast_ack_spec Σ iommu_broadcast_ack.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /iommu_broadcast_ack.
  (* allocation *)
  wp_apply wp_new; [done..|].
  iIntros (m) "(DEL & m & Hm)". rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "m" as "[m0 m1]".
  (* initializing *)
  wp_pures. rewrite shift_0. wp_write. wp_op. wp_write.

  (* constructing the invariant *)
  iMod UTok_alloc as (γ) "Tok".
  iMod (AtomicPtsTo_from_na with "m0") as (γx t V) "(#SeenV & SW & Pts)".
  iDestruct (AtomicSWriter_AtomicSync with "SW") as "#S".
  iDestruct (view_at_intro with "Pts") as (Vx) "[SeenVx Pts]".
  iMod (inv_alloc (iqN_ack m) _ (iq_ack_inv' ((m >> 0%nat)%stdpp) ((m >> 1%nat)%stdpp) γ γx)
          with "[Pts]") as "#Inv".
  { rewrite iq_ack_inv'_eq. iIntros "!>".
    iExists _, false, t, V, Vx. rewrite shift_0. by iFrame "Pts". }
  (* forking *)
  wp_apply (wp_fork with "[SW m1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write. wp_op. rewrite shift_0.
    (* open shared invariant *)
    iInv (iqN_ack m) as "INV" "Close". rewrite iq_ack_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts _]".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Pts SW") as %->.
    (* actual write of flag *)
    iApply (AtomicSWriter_release_write _ _ _ _ V Vx0 #1
              (((m >> 1%nat)%stdpp) ↦{1} #1)%I
              with "[$SW $Pts $m1 $SeenV]"); [solve_ndisj|..].
    iIntros "!>" (t1 V1) "(%MAX & SeenV' & [m1 SW'] & Pts')".
    (* reestablishing the invariant *)
    iMod ("Close" with "[-]"); last done.
    iIntros "!>". iExists _, true, t, V, _. iFrame "Pts'".
    iExists t1, V1. iSplit.
    { iPureIntro. split; [|done]. apply MAX. rewrite lookup_insert_eq. by eexists. }
    iRight. by iFrame "m1".

  - iIntros "_". wp_seq. wp_bind (repeat: _)%E.
    (* repeat loop *)
    iLöb as "IH". iApply wp_repeat; [done|].
    wp_op. rewrite shift_0.

    (* open shared invariant *)
    iInv (iqN_ack m) as "INV" "Close". rewrite iq_ack_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts Own]".

    (* actual read *)
    iApply (AtomicSeen_acquire_read with "[$Pts $SeenV]"); [solve_ndisj|..].
    { by iApply (AtomicSync_AtomicSeen with "S"). }
    iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Pts)".
    iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & MAX'' & LeV'').

    case (decide (t' = t0)) => [?|NEqt'].
    + subst t'.
      (* must have read the flag to be 0 *)
      iAssert (⌜v' = #0⌝)%I as %Eq0.
      { destruct b.
        - iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "_".
          iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert_ne in Sub2.
          + rewrite lookup_insert_eq in Sub2. by inversion Sub2.
          + clear -Lt1. intros ?. subst. lia.
        - iDestruct "Own" as %Eqζ'. iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert_eq in Sub2. by inversion Sub2. }
      (* keep looping *)
      iMod ("Close" with "[Pts Own]").
      { iIntros "!>". iExists ζ', b, t0, V0, _. by iFrame. }
      iIntros "!>". iExists 0. iSplit; [done|].
      iIntros "!> !>". by iApply ("IH" with "Post DEL Hm Tok SeenVx").

    + destruct b; last first.
      { (* b cannot be false *)
        iDestruct "Own" as %Eqζ'. exfalso.
        rewrite Eqζ' in Sub2.
        apply (lookup_weaken _ _ _ _ Eqt'), lookup_singleton_Some in Sub2 as [].
        by apply NEqt'. }
      iClear "IH".
      (* read 1: extract the data via the released view *)
      iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "Own".
      rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      have ? : t' = t1.
      { case (decide (t' = t1)) => [//|NEqt1].
        exfalso. by rewrite !lookup_insert_ne // in Sub2. }
      subst t'. rewrite lookup_insert_eq in Sub2. inversion Sub2. subst v' V'.

      iDestruct "Own" as "[Own|Data]".
      { iExFalso. by iDestruct (UTok_unique with "Tok Own") as "$". }
      iDestruct (view_at_elim with "[SV'] Data") as "Data".
      { iApply (monPred_in_mono with "SV'"). simpl. solve_lat. }

      iMod ("Close" with "[Pts Tok]").
      { iIntros "!>". iExists ζ', true, t0, V0, _. iFrame "Pts".
        iExists t1, V1. iSplit; [done|]. by iLeft. }
      iIntros "!>". iExists 1. iSplit; [done|].
      iIntros "!> !>".

      wp_pures. wp_read. by iApply "Post".
Qed.

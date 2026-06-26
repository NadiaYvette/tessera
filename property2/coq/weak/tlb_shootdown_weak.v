(* Tessera Property 2 / P2.4b — the cross-core use-after-free, ruled out under a GENUINE
   weak-memory base (iRC11 / ORC11), in gpfsl.

   The relaxed-memory analogue of ../tlb_shootdown.v (P2.3b, sequential consistency),
   and the weak-memory closure of the hazard the whole property is about: the unmapping
   core, *after the shootdown protocol completes*, FREES the frame (and may reuse it).
   Soundness is that no access races with that free — "core 0 waits for all acks before
   treating the page as free (and reusing the frame)" (kickoff P2.4 object, step 5).

     forked core  =  data := 42  ;;  flag <-ʳᵉˡ 1        (* write, then signal complete *)
     main core    =  repeat: !ᵃᶜ flag  ;;  v := !data ;; delete frame ;; v

   The `delete` is the reclamation.  It is safe *only because* the acquire-read of the
   flag synchronised with the release-write: that happens-before lets the main core
   recover full ownership of both cells (via view-token cancellation of the invariant)
   before freeing them.  Drop the release/acquire and the synchronisation — hence the
   safety of the free — is gone; this is the weak-memory form of the cross-core
   use-after-free the litmus family exhibits (../../litmus/) and that P2.3b ruled out
   under SC.

   Program: gpfsl-examples/mp/code.v (`mp_reclaim`).  Proof: gpfsl's
   `mp_instance_reclaim_gen_inv` (gpfsl-examples/mp/proof_gen_inv.v), re-derived here
   under the shootdown reading.  Uses `view_inv` cancellation (no one-shot token needed);
   all dependencies are in the installed gpfsl library. *)

From iris.proofmode Require Import proofmode monpred.
From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import lifting proofmode atomics view_invariants
                                 repeat_loop new_delete.  (* last: gpfsl's `delete` val
                                   must win over stdpp's map `delete` *)
Require Import iris.prelude.options.

(* ===== the program: gpfsl's mp_reclaim, framed as protocol-then-reclaim ===== *)
Notation flag := 0 (only parsing).
Notation data := 1 (only parsing).

Definition shootdown_reclaim : expr :=
  let: "m" := new [ #2] in
  "m" +ₗ #flag <- #0 ;;
  "m" +ₗ #data <- #0 ;;
  Fork ("m" +ₗ #data <- #42 ;;          (* the page-table / frame write *)
        "m" +ₗ #flag <-ʳᵉˡ #1) ;;       (* release: DSB-then-signal completion *)
  (repeat: !ᵃᶜ("m" +ₗ #flag)) ;;        (* acquire: wait for the ack (DSB+ISB) *)
  let: "v" := !("m" +ₗ #data) in         (* read the frame — provably 42 *)
  delete [ #2; "m"] ;;                    (* reclaim: free the frame, race-free *)
  "v".

Definition shootdown_spec Σ `{!noprolG Σ} (e : expr) :=
  ∀ tid, {{{ True }}} e @ tid; ⊤ {{{ v, RET #v; ⌜v = 42⌝ }}}.

Definition sdN (n : loc) := nroot .@ "sdrN" .@ n.

(* ===== invariant + proof (gpfsl reclaim variant, our naming) ===== *)
Implicit Types (x : loc) (γ : gname) (ζ : absHist) (t : time) (V : view).

Section inv.
Context `{!noprolG Σ, !atomicG Σ, !view_invG Σ}.
#[local] Notation vProp := (vProp Σ).

(* No one-shot token: the half view-tokens let the reader immediately cancel the
   invariant after acquiring y, recovering ownership of both cells for the free. *)
Definition sd_reclaim'_def (x y : loc) γx γi : vProp :=
  (∃ ζ (b : bool) t0 V0,
    x sw↦{γx} ζ ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
              @{V1} (y ↦ #42 ∗ view_tok γi (1/2))
    end
  )%I.
Definition sd_reclaim'_aux : seal (@sd_reclaim'_def). Proof. by eexists. Qed.
Definition sd_reclaim' := unseal (@sd_reclaim'_aux).
Definition sd_reclaim'_eq : @sd_reclaim' = _ := seal_eq _.

Definition sd_reclaim N x y γx γi :=
  view_inv γi N (sd_reclaim' x y γx γi).
End inv.

Lemma shootdown_reclaim_gen_inv `{!noprolG Σ, !view_invG Σ, !atomicG Σ} :
  shootdown_spec Σ shootdown_reclaim.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /shootdown_reclaim.
  (* allocation *)
  wp_apply wp_new; [done..|].
  iIntros (m) "(DEL & m & Hm)". rewrite own_loc_na_vec_cons own_loc_na_vec_singleton.
  iDestruct "m" as "[m0 m1]".
  (* initializing *)
  wp_pures. rewrite shift_0. wp_write. wp_op. wp_write.

  (* constructing the view invariant *)
  iMod (AtomicPtsTo_from_na with "m0") as (γx t V) "(#SeenV & SW & Pts)".
  iDestruct (AtomicSWriter_AtomicSync with "SW") as "#S".
  iMod (view_inv_alloc (sdN m) _) as (γi) "Inv".
  iMod ("Inv" $! (sd_reclaim' (m >> 0%nat) (m >> 1%nat) γx γi) with "[Pts]")
    as "(#Inv & vTok1 & vTok2)".
  { rewrite sd_reclaim'_eq. iIntros "!>".
    iExists _, false, t, V. rewrite shift_0. by iFrame "Pts". }
  (* forking *)
  wp_apply (wp_fork with "[SW m1 vTok1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write.
    wp_op. rewrite shift_0.
    (* open the view invariant *)
    iMod (view_inv_acc_base' with "[$Inv $vTok1]") as "(vTok1 & INV) {Inv}"; [done|].
    iDestruct "INV" as (Vb) "[INV Close]".
    rewrite {1}sd_reclaim'_eq.
    iDestruct "INV" as (ζ' b t0 V0) "[Pts _]".
    rewrite view_join_later. iDestruct "Pts" as ">Pts".
    iDestruct (view_join_elim' with "Pts SeenV") as (V') "(#SeenV' & % & Pts)".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Pts SW") as %->.
    (* release write of the flag, handing over data + half the view token *)
    iApply (AtomicSWriter_release_write _ _ _ _ V' _ #1
              ((m >> 1%nat) ↦{1} #42 ∗ view_tok γi (1 / 2))%I
              with "[$SW $Pts $m1 $vTok1 $SeenV']"); [solve_ndisj|..].
    iIntros "!>" (t1 V1) "((%MAX & %LeV1 & _) & SeenV1 & [[m1 vTok1] SW'] & Pts')".
    (* reestablish the invariant *)
    rewrite bi.and_elim_r bi.and_elim_l.
    iMod ("Close" $! V1 True%I with "vTok1 [-]"); last done.
    iIntros "vTok1 !>". iSplit; [|done].
    rewrite view_at_view_join. iNext. rewrite sd_reclaim'_eq.
    iExists _, true, t, V. iSplitL "Pts'"; first by iFrame.
    iExists t1, V1. iSplit.
    { iPureIntro. split; [|done]. apply MAX. rewrite lookup_insert_eq. by eexists. }
    by iFrame.

  - iIntros "_". wp_seq. wp_bind (repeat: _)%E.
    (* repeat loop *)
    iLöb as "IH". iApply wp_repeat; [done|].
    wp_op. rewrite shift_0.

    (* open the view invariant *)
    iMod (view_inv_acc_base' with "[$Inv $vTok2]") as "(vTok2 & INV) {Inv}"; [done|].
    iDestruct "INV" as (Vb) "[INV Close]".
    rewrite {1}sd_reclaim'_eq.
    iDestruct "INV" as (ζ' b t0 V0) "[Pts Own]".
    rewrite view_join_later. iDestruct "Pts" as ">Pts".

    (* acquire read of the flag *)
    iApply (AtomicSeen_acquire_read_vj with "[$Pts $SeenV]"); [solve_ndisj|..].
    { by iApply (AtomicSync_AtomicSeen with "S"). }
    iIntros "!>" (t' v' V' V'' ζ'') "(HF & #SV' & SN' & Pts)".
    iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & LeV'').

    case (decide (t' = t0)) => [?|NEqt'].
    + subst t'.
      (* read flag = 0: keep looping *)
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
      rewrite bi.and_elim_l.
      iMod ("Close" with "vTok2 [Pts Own]") as "vTok2".
      { iClear "IH". iNext. rewrite sd_reclaim'_eq.
        iExists ζ', b, t0, V0. iSplitL "Pts"; by iFrame. }
      iIntros "!>". iExists 0. iSplit; [done|].
      iIntros "!> !>". by iApply ("IH" with "Post DEL Hm vTok2").

    + destruct b; last first.
      { (* b cannot be false *)
        iDestruct "Own" as %Eqζ'. exfalso.
        rewrite Eqζ' in Sub2.
        apply (lookup_weaken _ _ _ _ Eqt'), lookup_singleton_Some in Sub2 as [].
        by apply NEqt'. }
      iClear "IH".
      (* read flag = 1: extract data + the other half token via the released view *)
      iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "Own".
      rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      have ? : t' = t1.
      { case (decide (t' = t1)) => [//|NEqt1].
        exfalso. by rewrite !lookup_insert_ne // in Sub2. }
      subst t'. rewrite lookup_insert_eq in Sub2. inversion Sub2. subst v' V'.

      rewrite view_join_view_at.
      iDestruct (view_at_elim with "[SV'] Own") as "[m1 vTok1]".
      { iApply (monPred_in_mono with "SV'"). simpl. solve_lat. }

      (* cancel the invariant: full ownership of both cells recovered for the free *)
      iCombine "vTok1" "vTok2" as "vTok".
      rewrite 2!bi.and_elim_r.
      iDestruct ("Close" with "vTok") as "[#LeVb >_]".
      iDestruct (view_join_elim with "Pts LeVb") as "Pts".
      iIntros "!>". iExists 1. iSplit; [done|]. simpl.
      iIntros "!> !>".

      wp_pures. wp_read. wp_let.

      (* reclaim: turn the atomic location back to non-atomic and free both cells *)
      iApply wp_hist_inv; [done|]. iIntros "HINV".
      iMod (AtomicPtsTo_to_na with "HINV Pts") as (t' v') "[m2 ?]"; [done|].
      wp_apply (wp_delete _ tid 2 m [v'; #42] with "[m1 m2 $DEL]"); [done|done|..].
      { rewrite own_loc_na_vec_cons own_loc_na_vec_singleton. by iFrame. }
      iIntros "_". wp_seq. by iApply ("Post" $! 42).
Qed.

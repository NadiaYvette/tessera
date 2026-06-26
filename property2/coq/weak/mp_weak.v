(* Tessera Property 2 / P2.4a — the shootdown's ordering core under a GENUINE
   weak-memory base (iRC11 / ORC11), in gpfsl.

   The relaxed-memory analogue of ../mp.v (P2.3a, which assumed sequential
   consistency).  ORC11 is release/acquire weak memory with per-thread *views*; the
   *release* store of the completion flag and the *acquire* load of it are what create
   the happens-before edge from the unmapping core's write to the remote core's read.

   Correspondence to the litmus necessity family (../../litmus/, P2.2):
     - release store  <-ʳᵉˡ   ==  P0's DSB after TLBI, before signalling completion
                                   (drop it -> shootdown-noP0dsb.litmus -> Sometimes)
     - acquire  load  !ᵃᶜ      ==  P1's DSB+ISB after seeing the flag, before the access
                                   (drop it -> shootdown-noP1bar.litmus -> Sometimes)
   With both present the reader provably observes the write; make either *relaxed* and
   the happens-before edge — hence this proof — is gone: ORC11 then admits the stale
   read.  That underivability is the proof-side twin of the litmus going Sometimes, and
   of the SC result `unmap_without_flush_breaks_coherence`.

   The program is gpfsl's own message-passing example (gpfsl-examples/mp/code.v); the
   proof is gpfsl's general-invariant proof (gpfsl-examples/mp/proof_gen_inv.v),
   re-derived here under the shootdown reading.  gpfsl's `examples` are not installed to
   the load path, so the one-shot token (uniq_token.v) is vendored below verbatim — it
   is just a sealed `own γ (Excl ())` over vProp. *)

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import lifting proofmode atomics view_invariants
                                 repeat_loop new_delete.
From iris.algebra Require Import excl.
From iris.base_logic Require Import lib.own.
From iris.proofmode Require Import proofmode monpred.
From gpfsl.base_logic Require Import vprop.
Require Import iris.prelude.options.

(* ===== vendored unique (one-shot) token — gpfsl-examples/uniq_token.v ===== *)
Class uniqTokG Σ := UniqTokG { uniq_tokG : inG Σ (exclR unitO); }.
Local Existing Instances uniq_tokG.
Definition uniqTokΣ : gFunctors := #[GFunctor (constRF (exclR unitO))].
Global Instance subG_uniqTokΣ {Σ} : subG uniqTokΣ Σ → uniqTokG Σ.
Proof. solve_inG. Qed.

Section Tok.
Context `{!uniqTokG Σ}.
Notation vProp := (vProp Σ).
Implicit Type (γ : gname).
Definition UTok_def γ : vProp := ⎡ own γ (Excl ()) ⎤%I.
Definition UTok_aux : seal (@UTok_def). Proof. by eexists. Qed.
Definition UTok := unseal (@UTok_aux).
Definition UTok_eq : @UTok = _ := seal_eq _.
#[global] Instance UTok_timeless γ : Timeless (UTok γ).
Proof. rewrite UTok_eq. apply _. Qed.
#[global] Instance UTok_affine γ : Affine (UTok γ).
Proof. rewrite UTok_eq. apply _. Qed.
#[global] Instance UTok_objective γ : Objective (UTok γ).
Proof. rewrite UTok_eq. apply _. Qed.
Lemma UTok_alloc_cofinite (G : gset gname) : ⊢ (|==> ∃ γ, ⌜γ ∉ G⌝ ∧ UTok γ : vProp)%I.
Proof.
  iStartProof.
  iMod (own_alloc_cofinite (Excl ()) G) as (γ) "[% U]"; [done|].
  iIntros "!>". iExists γ. rewrite UTok_eq. by iFrame "%∗".
Qed.
Lemma UTok_alloc : ⊢ (|==> ∃ γ, UTok γ : vProp)%I.
Proof.
  iStartProof. iMod (UTok_alloc_cofinite ∅) as (γ) "[_ U]".
  iIntros "!>". by iExists _.
Qed.
Lemma UTok_unique γ : UTok γ -∗ UTok γ -∗ False.
Proof. rewrite UTok_eq. iIntros "U1 U2". by iCombine "U1 U2" gives %?. Qed.
End Tok.

(* ===== the program: gpfsl's mp, framed as the shootdown ordering core =====
   P0 (the unmapping core): write the data (page-table / frame state), then RELEASE the
   completion flag.  P1 (the remote core): ACQUIRE-spin on the flag, then read. *)
Notation flag := 0 (only parsing).
Notation data := 1 (only parsing).

Definition shootdown_mp : expr :=
  let: "m" := new [ #2] in
  "m" +ₗ #flag <- #0 ;;
  "m" +ₗ #data <- #0 ;;
  Fork ("m" +ₗ #data <- #42 ;;          (* the page-table / frame write *)
        "m" +ₗ #flag <-ʳᵉˡ #1) ;;       (* release: DSB-then-signal completion *)
  (repeat: !ᵃᶜ("m" +ₗ #flag)) ;;        (* acquire: wait for completion (DSB+ISB) *)
  !("m" +ₗ #data).                        (* remote read — provably observes 42 *)

Definition shootdown_spec Σ `{!noprolG Σ} (e : expr) :=
  ∀ tid, {{{ True }}} e @ tid; ⊤ {{{ v, RET #v; ⌜v = 42⌝ }}}.

Definition sdN (n : loc) := nroot .@ "sdN" .@ n.

(* ===== invariant + proof (gpfsl-examples/mp/proof_gen_inv.v, our naming) ===== *)
Implicit Types (x : loc) (γ : gname) (ζ : absHist) (t : time) (V : view).

Section inv.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.
#[local] Notation vProp := (vProp Σ).

Definition sd_inv'_def (x y : loc) γ γx : vProp :=
  (∃ ζ (b : bool) t0 V0 Vx,
    @{Vx} (x sw↦{γx} ζ) ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
              (UTok γ ∨ @{V1} (y ↦ #42))
    end
  )%I.
Definition sd_inv'_aux : seal (@sd_inv'_def). Proof. by eexists. Qed.
Definition sd_inv' := unseal (@sd_inv'_aux).
Definition sd_inv'_eq : @sd_inv' = _ := seal_eq _.

#[global] Instance sd_inv'_objective x y γ γx : Objective (sd_inv' x y γ γx).
Proof.
  rewrite sd_inv'_eq.
  apply exists_objective=>?. apply exists_objective=>[[|]]; by apply _.
Qed.

Definition sd_inv N x y γ γx := inv N (sd_inv' x y γ γx).
End inv.

Lemma shootdown_mp_gen_inv `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ} :
  shootdown_spec Σ shootdown_mp.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /shootdown_mp.
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
  iMod (inv_alloc (sdN m) _ (sd_inv' (m >> 0%nat) (m >> 1%nat) γ γx)
          with "[Pts]") as "#Inv".
  { rewrite sd_inv'_eq. iIntros "!>".
    iExists _, false, t, V, Vx. rewrite shift_0. by iFrame "Pts". }
  (* forking *)
  wp_apply (wp_fork with "[SW m1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write. wp_op. rewrite shift_0.
    (* open shared invariant *)
    iInv (sdN m) as "INV" "Close". rewrite sd_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts _]".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Pts SW") as %->.
    (* actual write of flag *)
    iApply (AtomicSWriter_release_write _ _ _ _ V Vx0 #1 ((m >> 1%nat) ↦{1} #42)%I
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
    iInv (sdN m) as "INV" "Close". rewrite sd_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts Own]".

    (* actual read *)
    iApply (AtomicSeen_acquire_read with "[$Pts $SeenV]"); [solve_ndisj|..].
    { by iApply (AtomicSync_AtomicSeen with "S"). }
    iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Pts)".
    iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & LeV'').

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

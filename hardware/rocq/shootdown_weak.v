(* Tessera — Stage 2, S2.2a: the two-core shootdown ordering core over the concrete
   machine, under GENUINE weak memory (gpfsl / iRC11 / ORC11).

   This is the release/acquire lift of S2.1's broadcast, specialised to two cores and
   one direction, and it is the weak-memory analogue of mp_weak.v (P2.4a) with the
   toy message `#42` replaced by the *machine* PTE value `#(encode_pte invalid_pte)`:

       leader  =  pte <- #(encode_pte invalid_pte) ;; go <-ʳᵉˡ #1   (break-before-make,
                                                                     then RELEASE = DSB)
       remote  =  repeat !ᵃᶜ go ;; !pte                              (ACQUIRE = DSB+ISB,
                                                                     then read)

   The release/acquire pair creates the happens-before edge from the leader's PTE write
   to the remote's read, so the remote provably observes `#(encode_pte invalid_pte)`.
   Combined with `invalid_pte_not_valid` this is exactly "the remote sees the invalid
   page-table entry" — the ordering that lets it then clear its own TLB (S2.2b) and that
   makes "no core translates a freed frame" hold under relaxed memory.  Drop the rel/acq
   and the edge is gone; ORC11 admits the stale read (proof-side twin of
   `shootdown-noP0dsb` / `shootdown-noP1bar` going `Sometimes`, and of
   `unmap_without_flush_breaks_coherence`).

   gpfsl's value model is `LitPoison | LitLoc | LitInt` — there is no product/sum — so
   the PTE is bit-packed into a `Z` here (unlike S2.1's HeapLang nested-pair codec).
   The proof is gpfsl's general-invariant MP proof (gpfsl-examples/mp/proof_gen_inv.v),
   re-derived under the shootdown reading over the generated machine types; the one-shot
   token is vendored verbatim (gpfsl-examples/uniq_token.v) because gpfsl's examples are
   not installed to the load path. *)

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
Require Import machine_encoding. (* b2z, invalid_pte, invalid_pte_not_valid *)
Require Import iris.prelude.options.

(* ===== the machine PTE, bit-packed into a Z (gpfsl has no product values) =====
   [invalid_pte] / [invalid_pte_not_valid] / [b2z] come from machine_encoding.v. *)

(* Pack the 5 flag bits into the low 5 bits and the 44-bit PPN into the high bits. *)
Definition encode_pte (p : Pte) : Z :=
  (int_of_mword false p.(Pte_ppn)) * 32
  + b2z p.(Pte_valid) + 2 * b2z p.(Pte_read) + 4 * b2z p.(Pte_write)
  + 8 * b2z p.(Pte_exec) + 16 * b2z p.(Pte_user).

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

(* ===== the program: the shootdown ordering core, two cores =====
   cell 0 = go (the completion flag); cell 1 = pte (the page-table write). *)
Notation go := 0 (only parsing).
Notation pte := 1 (only parsing).

Definition shootdown_weak : expr :=
  let: "m" := new [ #2] in
  "m" +ₗ #go <- #0 ;;
  "m" +ₗ #pte <- #0 ;;
  Fork ("m" +ₗ #pte <- #(encode_pte invalid_pte) ;;   (* the break-before-make write *)
        "m" +ₗ #go <-ʳᵉˡ #1) ;;                       (* release: DSB-then-signal *)
  (repeat: !ᵃᶜ("m" +ₗ #go)) ;;                        (* acquire: wait for the write *)
  !("m" +ₗ #pte).                                     (* read — provably the invalid PTE *)

Definition shootdown_spec Σ `{!noprolG Σ} (e : expr) :=
  ∀ tid, {{{ True }}} e @ tid; ⊤ {{{ v, RET #v; ⌜v = encode_pte invalid_pte⌝ }}}.

Definition sdN (n : loc) := nroot .@ "sdN" .@ n.

(* ===== invariant + proof (gpfsl mp proof_gen_inv, machine PTE as the message) ===== *)
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
              (UTok γ ∨ @{V1} (y ↦ #(encode_pte invalid_pte)))
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

Lemma shootdown_weak_gen_inv `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ} :
  shootdown_spec Σ shootdown_weak.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /shootdown_weak.
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
  iMod (inv_alloc (sdN m) _ (sd_inv' ((m >> 0%nat)%stdpp) ((m >> 1%nat)%stdpp) γ γx)
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
    iApply (AtomicSWriter_release_write _ _ _ _ V Vx0 #1
              (((m >> 1%nat)%stdpp) ↦{1} #(encode_pte invalid_pte))%I
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
   S2.2b (part 1) — the remote -> leader ack round-trip.

   S2.2a proved leader -> remote (the PTE invalidation is observed).  This proves
   the reverse direction: the remote clears its TLB and RELEASES the ack; the
   leader ACQUIRE-spins on the ack and then reads the TLB, provably observing the
   cleared entry `encode_tlb None`.  Together the two directions are the two-core
   shootdown's happens-before graph.
   ============================================================ *)

(* option TlbEntry -> Z.  gpfsl's values are LitPoison|LitLoc|LitInt, so the
   entry is collapsed to the one bit the protocol needs here — cleared (None = 0)
   vs stale (Some = 1).  The full vpn/ppn/perm packing is deferred to the N-core
   reification (S2.2b part 2), which cites shootdown_correct. *)
Definition encode_tlb (o : option TlbEntry) : Z :=
  match o with None => 0 | Some _ => 1 end.

Lemma encode_tlb_None_ne_Some (e : TlbEntry) : encode_tlb None ≠ encode_tlb (Some e).
Proof. cbn. lia. Qed.

(* cell 0 = ack (the completion flag); cell 1 = tlb (the cleared entry). *)
Notation ack := 0 (only parsing).
Notation tlb := 1 (only parsing).

Definition shootdown_weak_ack : expr :=
  let: "m" := new [ #2] in
  "m" +ₗ #ack <- #0 ;;
  "m" +ₗ #tlb <- #0 ;;
  Fork ("m" +ₗ #tlb <- #(encode_tlb None) ;;   (* the TLB clear *)
        "m" +ₗ #ack <-ʳᵉˡ #1) ;;               (* release: DSB-then-ack *)
  (repeat: !ᵃᶜ("m" +ₗ #ack)) ;;                (* acquire: wait for the clear *)
  !("m" +ₗ #tlb).                              (* read — provably the cleared TLB *)

Definition shootdown_ack_spec Σ `{!noprolG Σ} (e : expr) :=
  ∀ tid, {{{ True }}} e @ tid; ⊤ {{{ v, RET #v; ⌜v = encode_tlb None⌝ }}}.

Definition sdN_ack (n : loc) := nroot .@ "sdNack" .@ n.

Section inv_ack.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ}.
#[local] Notation vProp := (vProp Σ).

Definition sd_ack_inv'_def (x y : loc) γ γx : vProp :=
  (∃ ζ (b : bool) t0 V0 Vx,
    @{Vx} (x sw↦{γx} ζ) ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
              (UTok γ ∨ @{V1} (y ↦ #(encode_tlb None)))
    end
  )%I.
Definition sd_ack_inv'_aux : seal (@sd_ack_inv'_def). Proof. by eexists. Qed.
Definition sd_ack_inv' := unseal (@sd_ack_inv'_aux).
Definition sd_ack_inv'_eq : @sd_ack_inv' = _ := seal_eq _.

#[global] Instance sd_ack_inv'_objective x y γ γx : Objective (sd_ack_inv' x y γ γx).
Proof.
  rewrite sd_ack_inv'_eq.
  apply exists_objective=>?. apply exists_objective=>[[|]]; by apply _.
Qed.

Definition sd_ack_inv N x y γ γx := inv N (sd_ack_inv' x y γ γx).
End inv_ack.

Lemma shootdown_weak_ack_gen_inv `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ} :
  shootdown_ack_spec Σ shootdown_weak_ack.
Proof.
  iIntros (tid Φ) "_ Post". rewrite /shootdown_weak_ack.
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
  iMod (inv_alloc (sdN_ack m) _ (sd_ack_inv' ((m >> 0%nat)%stdpp) ((m >> 1%nat)%stdpp) γ γx)
          with "[Pts]") as "#Inv".
  { rewrite sd_ack_inv'_eq. iIntros "!>".
    iExists _, false, t, V, Vx. rewrite shift_0. by iFrame "Pts". }
  (* forking *)
  wp_apply (wp_fork with "[SW m1]"); [done|..].
  - iIntros "!>" (tid').
    (* write message *)
    wp_op. wp_write. wp_op. rewrite shift_0.
    (* open shared invariant *)
    iInv (sdN_ack m) as "INV" "Close". rewrite sd_ack_inv'_eq.
    iDestruct "INV" as (ζ' b t0 V0 Vx0) "[>Pts _]".
    iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Pts SW") as %->.
    (* actual write of flag *)
    iApply (AtomicSWriter_release_write _ _ _ _ V Vx0 #1
              (((m >> 1%nat)%stdpp) ↦{1} #(encode_tlb None))%I
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
    iInv (sdN_ack m) as "INV" "Close". rewrite sd_ack_inv'_eq.
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

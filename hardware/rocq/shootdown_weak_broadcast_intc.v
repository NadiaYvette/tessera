(* Tessera — S2.5 (program, full controller in the loop): the N-core weak-memory
   broadcast shootdown whose IPI delivery is the interrupt controller's, not a
   bare `go` flag or hand-set mailbox.

   S2.4 (shootdown_weak_broadcast.v) gates every remote's flush on a single
   shared `go` flag, and reifies the IPI as the bare `deliver_ipi` ghost step
   (`bc_machine_ipi_step`).  S2.5's ghost bridge (intc_weak_broadcast.v) proved
   that `deliver_ipi` is realized by the controller's `intc_send`+`intc_ack`
   (`bc_machine_ipi_step_via_intc`).  This file is the *program* side: the
   controller's four bit-vectors (`Intc_pending`/`Intc_masked`/`Intc_delivery`/
   `Intc_ipi` from intc.sail) become four per-hart heap arrays
   `pending`/`masked`/`delivery`/`ipi`, and the remote's flush is gated on its
   own doorbell `ipi[i]`, produced by the leader's `intc_send` (release
   `pending[i]`) and the controller's delivery (`intc_ack`: pending ∧ ¬masked ∧
   delivery → pending:=0, ipi:=1).

   Program:

     leader  =  pte <- #invalid_pte ;;
                ∀ i. pending[i] <-ʳᵉˡ #1              (intc_send: latch pending, release)
                ;; fork N remotes ;; wait-all-acks
     remote i =  repeat !ᵃᶜ (pending[i]) ;;           (acquire: the IPI is pending)
                 intc_ack_op (pending∧¬masked∧delivery → pending:=0, ipi:=1)
                 ;; repeat !ᵃᶜ (ipi[i]) ;;             (acquire: observe the doorbell)
                 ;; tlb[i] <- #(encode_tlb None) ;;    (clear own TLB)
                 ;; ack[i] <-ʳᵉˡ #1                    (release ack: the clear is visible)

   The weak-memory chain is: PTE write ⟶ pending[i] release (leader) ⟶
   pending[i] acquire (remote) ⟶ ipi[i] release (ack) ⟶ ipi[i] acquire (remote),
   so the remote's TLB clear observes the invalid PTE — the
   `intc_ack ∘ intc_send = deliver_ipi` bridge made concrete in the program.

   `masked`/`delivery` are initialized once (all `#0` / all `#1`) and never
   change across the broadcast, so the ack's gate `pending ∧ ¬masked ∧ delivery`
   is live.  The interrupt-context delivery gate (`intc_enter_context` sets
   `delivery[i] := 0`) is where suppression would happen; it is left as the next
   increment on top of this file.

   See doc/stage2-shootdown.md (S2.5) and doc/system-state-goals.md (SSG-3). *)

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import lifting proofmode atomics view_invariants
                                 repeat_loop new_delete.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import own ghost_var.
From iris.proofmode Require Import proofmode monpred.
From gpfsl.base_logic Require Import vprop na meta_data.
From SailStdpp Require Import MachineWord.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import machine_encoding.   (* invalid_pte, leaf_entry *)
Require Import machine_reify.
Require Import coherence_leaf.
Require Import shootdown.
Require Import ipi.                (* deliver_ipi/receive_ipi *)
Require Import shootdown_weak.     (* encode_pte/encode_tlb, UTok, uniqTokG *)
Require Import tlb_tags.
Require Import shootdown_weak_broadcast. (* bc_machine, bc_wait_all, bc_init_acks, ack_cell *)
Require Import intc.
Require Import intc_types.
Require Import intc_proofs.        (* intc_receive_ipi_eq_deliver, Machine_with_ipi *)
Require Import intc_weak_broadcast. (* bc_machine_ipi_step_via_intc (the S2.5 pure reification) *)
Require Import iris.prelude.options.
Import ListNotations.

(* ============================================================
   The program: the interrupt controller as four per-hart heap arrays, plus the
   leader's send loop and the remote's ack → observe-doorbell → flush.
   ============================================================ *)

(* The controller's delivery step (`intc.intc_ack`): read masked[i], delivery[i];
   if ¬masked ∧ delivery then ring the doorbell ipi[i] (set #1), returning 1
   (delivered); else return 0 (no delivery).  The `pending` conjunct of
   intc.intc_ack's gate is established by the remote's prior `!ᵃᶜ` of pending[i]
   (it reads #1, so the IPI is pending), and intc.intc_ack's *clear* of pending
   is a ghost effect: no one re-reads pending[i] after the ack, so the heap
   write is unobservable and the leader applies intc_ack to the ghost Intc at
   wait time (reifying the mailbox).  The expression language has no `&&`/`¬`
   operators, so the gate is two nested `if:` (each `if: c then A else B` runs A
   iff c is nonzero). *)
Definition intc_ack_op : val :=
  λ: ["masked"; "delivery"; "ipi"; "i"],
    let: "m" := !("masked" +ₗ "i") in
    let: "d" := !("delivery" +ₗ "i") in
    if: "m" then #0
    else if: "d" then ("ipi" +ₗ "i") <- #1 ;; #1
         else #0.

(* The remote: acquire pending[i] (the IPI is sent), ack via the controller
   (delivery, gated on ¬masked ∧ delivery), observe its doorbell ipi[i], clear
   its TLB, release ack[i]. *)
Definition bc_remote_intc : val :=
  λ: ["pending"; "masked"; "delivery"; "ipi"; "ack"; "tlb"; "i"],
    (repeat: !ᵃᶜ("pending" +ₗ "i")) ;;
    intc_ack_op ["masked"; "delivery"; "ipi"; "i"] ;;
    (repeat: !("ipi" +ₗ "i")) ;;
    ("tlb" +ₗ "i") <- #(encode_tlb None) ;;
    ("ack" +ₗ "i") <-ʳᵉˡ #1.

(* Initialise the four controller arrays: pending := 0, masked := 0 (unmasked),
   delivery := 1 (delivery enabled), ipi := 0. *)
Definition bc_init_intc_arrays : val :=
  rec: "f" ["pending"; "masked"; "delivery"; "ipi"; "i"; "n"] :=
    if: "i" < "n"
    then ("pending" +ₗ "i") <- #0 ;;
         ("masked" +ₗ "i") <- #0 ;;
         ("delivery" +ₗ "i") <- #1 ;;
         ("ipi" +ₗ "i") <- #0 ;;
         "f" ["pending"; "masked"; "delivery"; "ipi"; ("i" + #1); "n"]
    else #☠.

(* The leader's send: latch (release) pending[i] for every core. *)
Definition bc_send_all : val :=
  rec: "f" ["pending"; "i"; "n"] :=
    if: "i" < "n"
    then ("pending" +ₗ "i") <-ʳᵉˡ #1 ;;
         "f" ["pending"; ("i" + #1); "n"]
    else #☠.

(* Fork one remote per core. *)
Definition bc_fork_remotes_intc : val :=
  rec: "f" ["pending"; "masked"; "delivery"; "ipi"; "ack"; "tlb"; "i"; "n"] :=
    if: "i" < "n"
    then (Fork (bc_remote_intc ["pending"; "masked"; "delivery"; "ipi"; "ack"; "tlb"; "i"]) ;;
          "f" ["pending"; "masked"; "delivery"; "ipi"; "ack"; "tlb"; ("i" + #1); "n"])
    else #☠.

(* The full device-in-the-loop broadcast. *)
Definition bc_broadcast_intc (n : nat) : expr :=
  let: "pte" := new [ #1] in
  let: "pending" := new [ #(Z.of_nat n)] in
  let: "masked" := new [ #(Z.of_nat n)] in
  let: "delivery" := new [ #(Z.of_nat n)] in
  let: "ipi" := new [ #(Z.of_nat n)] in
  let: "ack" := new [ #(Z.of_nat n)] in
  let: "tlb" := new [ #(Z.of_nat n)] in
  bc_init_intc_arrays ["pending"; "masked"; "delivery"; "ipi"; #0; #(Z.of_nat n)] ;;
  "pte" +ₗ #0 <- #(encode_pte invalid_pte) ;;  (* break-before-make *)
  bc_send_all ["pending"; #0; #(Z.of_nat n)] ;; (* send IPI to every core *)
  bc_init_acks ["ack"; #0; #(Z.of_nat n)] ;;
  bc_fork_remotes_intc ["pending"; "masked"; "delivery"; "ipi"; "ack"; "tlb";
                        #0; #(Z.of_nat n)] ;;
  bc_wait_all ["ack"; #0; #(Z.of_nat n)].

(* Application helpers, mirroring shootdown_weak_broadcast.v. *)
Definition bc_remote_intc_at (pending masked delivery ipi ack tlb : loc) (i : nat) : expr :=
  App bc_remote_intc [Lit (LitLoc pending); Lit (LitLoc masked); Lit (LitLoc delivery);
                      Lit (LitLoc ipi); Lit (LitLoc ack); Lit (LitLoc tlb);
                      Lit (LitInt (Z.of_nat i))].
Definition bc_broadcast_intc_at (n : nat) : expr := bc_broadcast_intc n.

(* ============================================================
   Ghost state: the abstract interrupt controller (the Intc record from
   intc.sail), held by the leader OUTSIDE the invariant and stepped in lockstep
   with the machine ghost — exactly as machine_ctx is for the machine.

   The pure reification is already proved in intc_weak_broadcast.v:
   [bc_machine_ipi_step_via_intc] says the leader's per-step ghost
   [receive_ipi (… (intc_ack (intc_send ic i) i) …)] is [bc_machine n (i+1)],
   i.e. the controller's send+ack realizes S2.4's [deliver_ipi].
   ============================================================ *)

Class intcG Σ := IntcG { intc_icG : ghost_varG Σ intc_types.Intc; }.
Local Existing Instance intc_icG.
Definition intcΣ : gFunctors := #[ghost_varΣ intc_types.Intc].
Global Instance subG_intcΣ {Σ} : subG intcΣ Σ → intcG Σ.
Proof. solve_inG. Qed.

Definition intc_ctx `{!intcG Σ} (γic : gname) (ic : intc_types.Intc) : vProp Σ :=
  ⎡ ghost_var γic (DfracOwn 1) ic ⎤.

#[global] Instance intc_ctx_objective `{!intcG Σ} γic ic : Objective (intc_ctx γic ic).
Proof. rewrite /intc_ctx. apply _. Qed.

Lemma intc_ctx_update `{!intcG Σ} (γic : gname) (ic ic' : intc_types.Intc) :
  intc_ctx γic ic ⊢ |==> intc_ctx γic ic' : vProp Σ.
Proof.
  rewrite /intc_ctx. iIntros "Hic".
  iMod (ghost_var_update ic' γic ic with "Hic") as "Hic'".
  iIntros "!>". by iFrame.
Qed.

(* bool → Z, matching the heap cells' {0,1} encoding (intc_send/ack set/clear
   individual bits; the program stores them as #0/#1). *)
Definition bit_z (b : bool) : Z := if b then 1 else 0.

(* The controller's per-hart heap cell: the four arrays pending/masked/delivery/
   ipi agree, at index i, with the abstract Intc record's bits.  Held inside the
   broadcast invariant (shared between leader and remote i). *)
Definition intc_cell `{!noprolG Σ} (pending masked delivery ipi : loc) (ic : intc_types.Intc) (i : nat) : vProp Σ :=
  (pending >> i)%stdpp ↦ #(bit_z (intc.intc_get_bit (intc_types.Intc_pending ic) (Z.of_nat i) false)) ∗
  (masked >> i)%stdpp ↦ #(bit_z (intc.intc_get_bit (intc_types.Intc_masked ic) (Z.of_nat i) false)) ∗
  (delivery >> i)%stdpp ↦ #(bit_z (intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat i) false)) ∗
  (ipi >> i)%stdpp ↦ #(bit_z (intc.intc_get_bit (intc_types.Intc_ipi ic) (Z.of_nat i) false)).

(* Application helpers for the remaining program phases. *)
Definition bc_init_intc_arrays_at (pending masked delivery ipi : loc) (i n : nat) : expr :=
  App bc_init_intc_arrays [Lit (LitLoc pending); Lit (LitLoc masked); Lit (LitLoc delivery);
                           Lit (LitLoc ipi); Lit (LitInt (Z.of_nat i)); Lit (LitInt (Z.of_nat n))].
Definition bc_send_all_at (pending : loc) (i n : nat) : expr :=
  App bc_send_all [Lit (LitLoc pending); Lit (LitInt (Z.of_nat i)); Lit (LitInt (Z.of_nat n))].
Definition bc_fork_remotes_intc_at (pending masked delivery ipi ack tlb : loc) (i n : nat) : expr :=
  App bc_fork_remotes_intc [Lit (LitLoc pending); Lit (LitLoc masked); Lit (LitLoc delivery);
                            Lit (LitLoc ipi); Lit (LitLoc ack); Lit (LitLoc tlb);
                            Lit (LitInt (Z.of_nat i)); Lit (LitInt (Z.of_nat n))].

(* ============================================================
   The controller-array initialisation: pending := 0, masked := 0 (unmasked),
   delivery := 1 (delivery enabled), ipi := 0, for each core.  Mirrors
   bc_init_acks_spec, with four cells per core instead of one.
   ============================================================ *)

Section bc_inv_intc.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ, !bcG Σ, !intcG Σ}.

Lemma bc_init_intc_arrays_spec (pending masked delivery ipi : loc) :
  ∀ (i n : nat) tid,
  {{{ [∗ set] j ∈ (all_cores n ∖ all_cores i),
        (pending >> j) ↦ #☠ ∗ (masked >> j) ↦ #☠ ∗ (delivery >> j) ↦ #☠ ∗ (ipi >> j) ↦ #☠ }}}
    bc_init_intc_arrays_at pending masked delivery ipi i n @ tid; ⊤
  {{{ RET #☠; [∗ set] j ∈ (all_cores n ∖ all_cores i),
        (pending >> j) ↦ #0 ∗ (masked >> j) ↦ #0 ∗ (delivery >> j) ↦ #1 ∗ (ipi >> j) ↦ #0 }}}.
Proof.
  iIntros (i n tid Φ) "Harr HΦ".
  rewrite /bc_init_intc_arrays_at /bc_init_intc_arrays.
  iLöb as "IH" forall (i Φ).
  wp_lam.
  destruct (decide (i < n)) as [Hin | Hnot].
  - wp_op. rewrite bool_decide_true; [|lia]. wp_if.
    rewrite (all_cores_step n i Hin).
    rewrite big_sepS_union; last first.
    { apply singleton_notin_diff. exact Hin. }
    rewrite big_sepS_singleton.
    iDestruct "Harr" as "[Hcell Hrest]".
    iDestruct "Hcell" as "(Hp & Hm & Hd & Hq)".
    wp_op. rewrite Nat2Z.id. wp_write. (* pending[i] := 0 *)
    wp_op. rewrite Nat2Z.id. wp_write. (* masked[i] := 0 *)
    wp_op. rewrite Nat2Z.id. wp_write. (* delivery[i] := 1 *)
    wp_op. rewrite Nat2Z.id. wp_write. (* ipi[i] := 0 *)
    wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
    iApply ("IH" $! (i + 1)%nat Φ with "Hrest").
    iIntros "!> Hrest'".
    iApply "HΦ".
    rewrite big_sepS_union; last first.
    { apply singleton_notin_diff. exact Hin. }
    rewrite big_sepS_singleton. iFrame.
  - wp_op. rewrite bool_decide_false; [|lia]. wp_if.
    rewrite (all_cores_diff_empty n i); [|lia].
    rewrite big_sepS_empty. by iApply "HΦ".
Qed.

End bc_inv_intc.

(* ============================================================
   The leader's send: release (send) pending[i] for every core, mirroring the
   single `go <-ʳᵉˡ #1` in bc_broadcast_spec.  Each release leaves the cell in
   go_released (history {t0:#0} extended with {t1:#1}), which the remote then
   acquires.  The controller's Intc_pending bit is latched by this release (the
   intc_send); the ghost is stepped by the leader in the broadcast spec.
   ============================================================ *)

Section bc_send.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ, !bcG Σ, !intcG Σ}.

Lemma bc_send_all_spec (pending : loc) :
  ∀ (γp : nat → gname) (t : nat → positive) (V : nat → view) (i n : nat) tid,
  {{{ [∗ set] j ∈ (all_cores n ∖ all_cores i),
        (pending >> j) sw⊒{γp j} {[t j := (#0, V j)]} ∗
        (pending >> j) sw↦{γp j} {[t j := (#0, V j)]} ∗
        ⊒(V j) }}}
    bc_send_all_at pending i n @ tid; ⊤
  {{{ RET #☠; [∗ set] j ∈ (all_cores n ∖ all_cores i),
        go_released (pending >> j) (γp j) }}}.
Proof.
  iIntros (γp t V i n tid Φ) "Hp HΦ".
  rewrite /bc_send_all_at /bc_send_all.
  iLöb as "IH" forall (i Φ).
  wp_lam.
  destruct (decide (i < n)) as [Hin | Hnot].
  - wp_op. rewrite bool_decide_true; [|lia]. wp_if.
    rewrite (all_cores_step n i Hin).
    rewrite big_sepS_union; last first.
    { apply singleton_notin_diff. exact Hin. }
    rewrite big_sepS_singleton.
    iDestruct "Hp" as "[Hcell Hrest]".
    iDestruct "Hcell" as "(SW_i & Pts_i & SV_i)".
    iDestruct (view_at_intro with "Pts_i") as (Vx) "[_ Pts_i]".
    wp_op. rewrite Nat2Z.id.
    wp_apply (AtomicSWriter_release_write _ _ _ _ (V i) Vx #1 True%I
                with "[$SW_i $Pts_i $SV_i]"); [solve_ndisj|..].
    iIntros (t1 V1) "(%MAX & _ & [_ SW_i'] & Pts_i')".
    iAssert (go_released (pending >> i) (γp i))%I with "[Pts_i']" as "Hrel".
    { rewrite go_released_eq. iExists _, (t i), t1, (V i), V1, _. iFrame "Pts_i'".
      iPureIntro. split; [|done]. destruct MAX as [Hfresh _]. apply Hfresh.
      rewrite lookup_insert_eq. by eexists. }
    wp_seq.
    wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
    iApply ("IH" $! (i + 1)%nat Φ with "Hrest").
    iIntros "!> Hrest'".
    iApply "HΦ".
    rewrite big_sepS_union; last first.
    { apply singleton_notin_diff. exact Hin. }
    rewrite big_sepS_singleton. iFrame.
  - wp_op. rewrite bool_decide_false; [|lia]. wp_if.
    rewrite (all_cores_diff_empty n i); [|lia].
    rewrite big_sepS_empty. by iApply "HΦ".
Qed.

End bc_send.

(* ============================================================
   The broadcast invariant (device-in-the-loop): the sent pending cells
   (go_released, one per core) and the per-core ack cells.  masked/delivery/ipi
   are NA cells held by the remote (not shared), so they live outside the
   invariant and are transferred to the remote at fork time.
   ============================================================ *)

(* ============================================================
   Pure lemmas for the leader's controller-ghost step: [intc_ack ∘ intc_send]
   advances the delivered-bit prefix and preserves the pending/masked/delivery
   shape.  [intc_step_ok] is the loop invariant threaded through bc_wait_all.
   ============================================================ *)

(* [intc_set_bit] is structurally recursive on the list, so it preserves length. *)
Lemma intc_set_bit_length (l : list bool) (i : Z) (v : bool) :
  length (intc.intc_set_bit l i v) = length l.
Proof.
  revert i. induction l as [| b bs IH]; intros i; cbn [intc.intc_set_bit length].
  - reflexivity.
  - destruct (Z.eqb i 0); cbn [length]; [reflexivity | f_equal; apply IH].
Qed.

(* [intc_ack] copies the masked/delivery fields verbatim (it only touches
   pending and ipi), so it preserves both. *)
Lemma intc_ack_preserves_masked (ic : intc_types.Intc) (i : Z) :
  intc_types.Intc_masked (intc.intc_ack ic i) = intc_types.Intc_masked ic.
Proof.
  unfold intc.intc_ack.
  destruct (andb (intc.intc_get_bit (intc_types.Intc_pending ic) i false)
                 (andb (negb (intc.intc_get_bit (intc_types.Intc_masked ic) i false))
                       (intc.intc_get_bit (intc_types.Intc_delivery ic) i false)));
  cbn; reflexivity.
Qed.

Lemma intc_ack_preserves_delivery (ic : intc_types.Intc) (i : Z) :
  intc_types.Intc_delivery (intc.intc_ack ic i) = intc_types.Intc_delivery ic.
Proof.
  unfold intc.intc_ack.
  destruct (andb (intc.intc_get_bit (intc_types.Intc_pending ic) i false)
                 (andb (negb (intc.intc_get_bit (intc_types.Intc_masked ic) i false))
                       (intc.intc_get_bit (intc_types.Intc_delivery ic) i false)));
  cbn; reflexivity.
Qed.

(* The abstract interrupt-controller state at broadcast step i: core i's mailbox
   is exactly the delivered-bit prefix, every pending line is flat, and every
   hart is unmasked with delivery enabled (the state bc_broadcast initialises). *)
Definition intc_step_ok (ic : intc_types.Intc) (n i : nat) : Prop :=
  intc_types.Intc_ipi ic = ipi_prefix n i ∧
  length (intc_types.Intc_pending ic) = n ∧
  (∀ (j : nat), Nat.lt j n → intc.intc_get_bit (intc_types.Intc_masked ic) (Z.of_nat j) false = false) ∧
  (∀ (j : nat), Nat.lt j n → intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat j) false = true).

(* One controller step: send (latch pending) then ack (deliver) core i advances
   the delivered-bit prefix by one and preserves the invariant. *)
Lemma intc_step_ok_step (ic : intc_types.Intc) (n i : nat) (Hin : Nat.lt i n) :
  intc_step_ok ic n i →
  intc_step_ok (intc.intc_ack (intc.intc_send ic (Z.of_nat i)) (Z.of_nat i)) n (i + 1).
Proof.
  intros (Hipi & Hlen & Hm & Hd).
  set (ic' := intc.intc_send ic (Z.of_nat i)).
  set (ic'' := intc.intc_ack ic' (Z.of_nat i)).
  split; [| split; [| split ]].
  - subst ic'' ic'. rewrite (intc_ack_unmasked_rings (intc.intc_send ic (Z.of_nat i)) i).
    + rewrite (intc_send_preserves_ipi ic (Z.of_nat i)). rewrite Hipi.
      rewrite (intc_set_bit_eq_list_update_bool (ipi_prefix n i) (Z.of_nat i) true).
      assert (Hinz : Z.lt (Z.of_nat i) (Z.of_nat n)) by lia.
      rewrite <- (ipi_prefix_step n i Hinz). reflexivity.
    + apply intc_send_sets_pending. rewrite Hlen. exact Hin.
    + rewrite (intc_send_preserves_masked ic (Z.of_nat i)). apply Hm. exact Hin.
    + rewrite (intc_send_preserves_delivery ic (Z.of_nat i)). apply Hd. exact Hin.
  - subst ic'' ic'. rewrite (intc_ack_unmasked_clears_pending (intc.intc_send ic (Z.of_nat i)) i).
    + rewrite intc_set_bit_length.
      unfold intc.intc_send. cbn.
      rewrite intc_set_bit_length. exact Hlen.
    + apply intc_send_sets_pending. rewrite Hlen. exact Hin.
    + rewrite (intc_send_preserves_masked ic (Z.of_nat i)). apply Hm. exact Hin.
    + rewrite (intc_send_preserves_delivery ic (Z.of_nat i)). apply Hd. exact Hin.
  - intros j Hjn. subst ic'' ic'.
    rewrite (intc_ack_preserves_masked (intc.intc_send ic (Z.of_nat i)) (Z.of_nat i)).
    rewrite (intc_send_preserves_masked ic (Z.of_nat i)). apply Hm. exact Hjn.
  - intros j Hjn. subst ic'' ic'.
    rewrite (intc_ack_preserves_delivery (intc.intc_send ic (Z.of_nat i)) (Z.of_nat i)).
    rewrite (intc_send_preserves_delivery ic (Z.of_nat i)). apply Hd. exact Hjn.
Qed.

(* The delivered-bit prefix is saturated for i ≥ n, so [intc_step_ok n i]
   coincides with [intc_step_ok n n] once the loop is exhausted. *)
Lemma ipi_prefix_ge (n i : nat) (H : n ≤ i) : ipi_prefix n i = ipi_prefix n n.
Proof.
  unfold ipi_prefix. apply List.map_ext_in. intros j Hj.
  apply in_seq in Hj as [_ Hjn].
  rewrite !bool_decide_true; [reflexivity | lia | lia].
Qed.

Section bc_remote_intc.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ, !bcG Σ, !intcG Σ}.
Context (γm : gname) (root : mword 44) (va : mword 64) (mem : list MemEntry).
#[local] Abbreviation vProp := (vProp Σ).

Definition bc_inv_intc_def (γp γtok γack : nat → gname) (pending ack tlb : loc) (n : nat) : vProp :=
  ([∗ set] j ∈ all_cores n,
     go_released (pending >> j) (γp j) ∗
     ack_cell va (ack >> j) (tlb >> j) (γtok j) (γack j))%I.
Definition bc_inv_intc_aux : seal (@bc_inv_intc_def). Proof. by eexists. Qed.
Definition bc_inv_intc := unseal bc_inv_intc_aux.
Definition bc_inv_intc_eq : @bc_inv_intc = _ := seal_eq _.

#[global] Instance bc_inv_intc_objective γp γtok γack pending ack tlb n :
  Objective (bc_inv_intc γp γtok γack pending ack tlb n).
Proof.
  rewrite bc_inv_intc_eq. apply _.
Qed.

Definition bc_N_intc (pending : loc) := nroot .@ "bcIntcN" .@ pending.
Definition bc_inv_intc_ctx (γp γtok γack : nat → gname) (pending ack tlb : loc) (n : nat) :=
  inv (bc_N_intc pending) (bc_inv_intc γp γtok γack pending ack tlb n).

(* ============================================================
   The remote: acquire pending[i] (the IPI is sent), ack via the controller
   (gate on ¬masked ∧ delivery, then ring the doorbell), observe the doorbell,
   clear own TLB, release ack[i].
   ============================================================ *)

Lemma bc_remote_intc_spec (γp γtok γack : nat → gname)
    (pending masked delivery ipi ack tlb : loc) (i n : nat) :
  ∀ (ζp : absHist) (t_i : positive) (V : view) tid,
  {{{ ⌜i < n⌝ ∗ bc_inv_intc_ctx γp γtok γack pending ack tlb n ∗
      (pending >> i) sy⊒{γp i} ζp ∗ ⊒V ∗
      (masked >> i) ↦ #0 ∗ (delivery >> i) ↦ #1 ∗ (ipi >> i) ↦ #0 ∗
      (ack >> i) sw⊒{γack i} {[t_i := (#0, V)]} ∗ (tlb >> i) ↦ #☠ }}}
    bc_remote_intc_at pending masked delivery ipi ack tlb i @ tid; ⊤
  {{{ RET #☠; True }}}.
Proof.
  iIntros (ζp t_i V tid Φ) "(%Hi & #HI & #Sp & #SV & Hm & Hd & Hq & SWack & Htlb) HΦ".
  rewrite /bc_remote_intc_at /bc_remote_intc.
  wp_lam.
  (* -------- acquire pending[i] (repeat until #1) -------- *)
  wp_bind (repeat: !ᵃᶜ(#pending +ₗ #i))%E.
  iLöb as "IH".
  iApply wp_repeat; [done|].
  wp_op. rewrite Nat2Z.id.
  iInv (bc_N_intc pending) as "INV" "Close". rewrite bc_inv_intc_eq.
  iDestruct (big_sepS_delete _ (all_cores n) i with "INV") as "[Hcell INV_rest]".
  { rewrite elem_of_all_cores. exact Hi. }
  iDestruct "Hcell" as "[Hrel Hack]".
  rewrite go_released_eq.
  iDestruct "Hrel" as (ζ t0 t1 V0 V1 Vx) "[>Pts Hpure]".
  iApply (AtomicSeen_acquire_read with "[$Pts $SV]"); [solve_ndisj|..].
  { by iApply (AtomicSync_AtomicSeen with "Sp"). }
  iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Pts)".
  iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & MAX'' & LeV'').
  case (decide (t' = t0)) => [Ht0|NEqt0].
  - subst t'. (* read #0 — keep looping *)
    iAssert (⌜v' = #0⌝)%I as %Eq0.
    { iDestruct "Hpure" as "[%Lt1 %Hζ]".
      iPureIntro.
      rewrite Hζ in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      rewrite lookup_insert_ne in Sub2.
      + rewrite lookup_insert_eq in Sub2. by inversion Sub2.
      + clear -Lt1. intros ?. subst. lia. }
    iMod ("Close" with "[Pts Hpure INV_rest Hack]").
    { iIntros "!>". rewrite /bc_inv_intc_def. iApply (big_sepS_delete _ (all_cores n) i).
      { rewrite elem_of_all_cores. exact Hi. }
      rewrite go_released_eq. iFrame "INV_rest". iSplitL "Pts Hpure"; [|iFrame "Hack"].
      iExists ζ, t0, t1, V0, V1, _. iFrame "Pts Hpure". }
    iIntros "!>". iExists 0. iSplit; [done|].
    iIntros "!> !>". by iApply ("IH" with "Hm Hd Hq SWack Htlb HΦ").
  - (* read #1 — proceed *)
    iDestruct "Hpure" as "[%Lt1 %Hζ]".
    rewrite Hζ in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
    have Ht1 : t' = t1.
    { case (decide (t' = t1)) => [//|NEqt1].
      exfalso. by rewrite !lookup_insert_ne // in Sub2. }
    subst t'.
    rewrite lookup_insert_eq in Sub2. inversion Sub2. subst v'.
    iMod ("Close" with "[Pts INV_rest Hack]").
    { iIntros "!>". rewrite /bc_inv_intc_def. iApply (big_sepS_delete _ (all_cores n) i).
      { rewrite elem_of_all_cores. exact Hi. }
      rewrite go_released_eq. iFrame "INV_rest". iSplitL "Pts"; [|iFrame "Hack"].
      iExists ζ, t0, t1, V0, V1, _. iFrame "Pts".
      iPureIntro. split; [exact Lt1|exact Hζ]. }
    iIntros "!>". iExists 1. iSplit; [done|]. iIntros "!> !>". wp_seq.
  (* -------- the ack: read masked[i], delivery[i], ring the doorbell -------- *)
  rewrite /intc_ack_op.
  wp_lam.
  wp_op. rewrite Nat2Z.id. wp_read. wp_let.   (* m := !(masked+i) = #0 *)
  wp_op. rewrite Nat2Z.id. wp_read. wp_let.   (* d := !(delivery+i) = #1 *)
  wp_if.                                     (* m = #0 → else branch *)
  wp_if.                                     (* d = #1 → then branch *)
  wp_op. rewrite Nat2Z.id. wp_write.         (* ipi[i] := #1 *)
  wp_seq.
  (* -------- observe the doorbell (repeat ! ipi[i]) -------- *)
  wp_bind (repeat: !(#ipi +ₗ #i))%E.
  iLöb as "IHq".
  iApply wp_repeat; [done|].
  wp_op. rewrite Nat2Z.id. wp_read.
  iExists 1. iSplit; [done|]. iIntros "!> !>". wp_seq.
  (* -------- clear own TLB -------- *)
  wp_op. rewrite Nat2Z.id. wp_write.
  (* -------- release ack[i] (deposit the cleared tlb) -------- *)
  wp_op. rewrite Nat2Z.id.
  iInv (bc_N_intc pending) as "INV" "Close". rewrite bc_inv_intc_eq.
  iDestruct (big_sepS_delete _ (all_cores n) i with "INV") as "[Hcell INV_rest]".
  { rewrite elem_of_all_cores. exact Hi. }
  iDestruct "Hcell" as "[Hrel Hack]".
  rewrite ack_cell_eq.
  iDestruct "Hack" as (ζa b ta0 Va0 Vax) "[>Ptsa >Own]".
  iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Ptsa SWack") as %->.
  destruct b.
  + iDestruct "Own" as (tb Vb [Ltb Hb]) "_".
    exfalso. exact (singleton_ne_released t_i ta0 tb V Va0 Vb Ltb Hb).
  + iDestruct "Own" as %Hown0.
    iApply (AtomicSWriter_release_write _ _ _ _ V Vax #1
              ((tlb >> i) ↦{1} #(encode_tlb None))%I
              with "[$SWack $Ptsa $Htlb $SV]"); [solve_ndisj|..].
    iIntros "!>" (t1' V1') "(%MAX & SeenV1' & [Htlb SWack'] & Ptsa')".
    iMod ("Close" with "[Hrel INV_rest Ptsa' Htlb]"); last first.
    { iIntros "!>". by iApply "HΦ". }
    iIntros "!>". rewrite /bc_inv_intc_def. iApply (big_sepS_delete _ (all_cores n) i).
    { rewrite elem_of_all_cores. exact Hi. }
    rewrite go_released_eq. rewrite ack_cell_eq. iFrame "INV_rest". iSplitL "Hrel"; [done|].
    iExists _, true, t_i, V, _. iFrame "Ptsa'".
    iExists t1', V1'. iSplit.
    { iPureIntro. split; [|done]. apply MAX. rewrite lookup_insert_eq. by eexists. }
    iRight. rewrite (flush_tlb_entry_leaf va). by iFrame "Htlb".
Qed.

(* ============================================================
   Fork one remote per core, handing each the controller cells (masked/delivery/
   ipi) and the ack/tlb cells, plus the shared pending reader-sync and view.
   ============================================================ *)

Lemma bc_fork_remotes_intc_spec (γp γtok γack : nat → gname)
    (pending masked delivery ipi ack tlb : loc) :
  ∀ (t : nat → positive) (V : nat → view) (i n : nat) tid,
  {{{ bc_inv_intc_ctx γp γtok γack pending ack tlb n ∗
      bc_sync_ctx γack ack t V n ∗
      [∗ set] j ∈ (all_cores n ∖ all_cores i),
        (pending >> j) sy⊒{γp j} {[t j := (#0, V j)]} ∗
        (masked >> j) ↦ #0 ∗ (delivery >> j) ↦ #1 ∗ (ipi >> j) ↦ #0 ∗
        (ack >> j) sw⊒{γack j} {[t j := (#0, V j)]} ∗ (tlb >> j) ↦ #☠ }}}
    bc_fork_remotes_intc_at pending masked delivery ipi ack tlb i n @ tid; ⊤
  {{{ RET #☠; True }}}.
Proof.
  iIntros (t V i n tid Φ) "(#HI & #Sctx & Hrest) HΦ".
  rewrite /bc_fork_remotes_intc_at /bc_fork_remotes_intc.
  iLöb as "IH" forall (i Φ).
  wp_lam.
  destruct (decide (i < n)) as [Hin | Hnot].
  - wp_op. rewrite bool_decide_true; [|lia]. wp_if.
    rewrite (all_cores_step n i Hin).
    rewrite big_sepS_union; last first.
    { apply singleton_notin_diff. exact Hin. }
    rewrite big_sepS_singleton.
    iDestruct "Hrest" as "[Hrest_i Hrest']".
    iDestruct "Hrest_i" as "(#S_i & Hm_i & Hd_i & Hq_i & SWack_i & Htlb_i)".
    iDestruct (big_sepS_elem_of _ (all_cores n) i with "Sctx") as "#[_ SV_i]".
    { rewrite elem_of_all_cores. exact Hin. }
    wp_apply (wp_fork with "[Hm_i Hd_i Hq_i SWack_i Htlb_i]"); [done|..].
    + iIntros "!>" (tid').
      iApply (bc_remote_intc_spec γp γtok γack pending masked delivery ipi ack tlb i n
                {[t i := (#0, V i)]} (t i) (V i) tid'
                with "[$HI $S_i $SV_i $Hm_i $Hd_i $Hq_i $SWack_i $Htlb_i]").
      { iPureIntro. exact Hin. }
      iIntros "!> _". done.
    + iIntros "_". wp_seq.
      wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
      iApply ("IH" $! (i + 1)%nat Φ with "Hrest'").
      iIntros "!> _". by iApply "HΦ".
  - wp_op. rewrite bool_decide_false; [|lia]. wp_if.
    by iApply "HΦ".
Qed.

(* ============================================================
   The leader's ack wait, with the interrupt controller in the loop: as each
   core acks, the leader steps the machine ghost through the controller's
   send+ack (bc_machine_ipi_step_via_intc) and the abstract Intc ghost in
   lockstep.
   ============================================================ *)

Lemma bc_wait_all_intc_spec (γic : gname) (γp γtok γack : nat → gname)
    (pending ack tlb : loc) :
  ∀ (ic : intc_types.Intc) (t : nat → positive) (V : nat → view) (i n : nat) tid,
  {{{ machine_ctx γm (bc_machine root va mem n i) ∗
      intc_ctx γic ic ∗ ⌜intc_step_ok ic n i⌝ ∗
      bc_inv_intc_ctx γp γtok γack pending ack tlb n ∗
      bc_sync_ctx γack ack t V n }}}
    bc_wait_all_at ack i n @ tid; ⊤
  {{{ RET #☠; machine_ctx γm (bc_post_machine root va mem n) ∗
      ∃ ic', intc_ctx γic ic' ∗ ⌜intc_step_ok ic' n n⌝ }}}.
Proof.
  iIntros (ic t V i n tid Φ) "(Hmach & Hic & Hok & #HI & #Sctx) HΦ".
  rewrite /bc_wait_all_at /bc_wait_all.
  iLöb as "IH" forall (ic i Φ) "Hok".
  iDestruct "Hok" as %Hok.
  wp_lam.
  destruct (decide (i < n)) as [Hin | Hnot].
  - (* i < n: acquire ack[i], then recurse *)
    assert (HinN : Nat.lt i n) by lia.
    wp_op. rewrite bool_decide_true; [|lia]. wp_if.
    iDestruct (big_sepS_elem_of _ (all_cores n) i with "Sctx") as "#[S_i SV_i]".
    { rewrite elem_of_all_cores. exact Hin. }
    (* -------- acquire ack[i] (repeat until #1) -------- *)
    wp_bind (repeat: !ᵃᶜ(#ack +ₗ #i))%E.
    iLöb as "IHack".
    iApply wp_repeat; [done|].
    wp_op. rewrite Nat2Z.id.
    iInv (bc_N_intc pending) as "INV" "Close". rewrite bc_inv_intc_eq.
    iDestruct (big_sepS_delete _ (all_cores n) i with "INV") as "[Hcell INV_rest]".
    { rewrite elem_of_all_cores. exact Hin. }
    iDestruct "Hcell" as "[Hrel Hack]".
    rewrite ack_cell_eq.
    iDestruct "Hack" as (ζa b ta0 Va0 Vax) "[>Ptsa >Own]".
    iApply (AtomicSeen_acquire_read with "[$Ptsa $SV_i]"); [solve_ndisj|..].
    { by iApply (AtomicSync_AtomicSeen with "S_i"). }
    iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Ptsa)".
    iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & MAX'' & LeV'').
    case (decide (t' = ta0)) => [Hta0 | NEqta0].
    + (* read #0 — keep looping *)
      subst t'.
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
      iMod ("Close" with "[Hrel INV_rest Ptsa Own]").
      { iIntros "!>". rewrite /bc_inv_intc_def. iApply (big_sepS_delete _ (all_cores n) i).
        { rewrite elem_of_all_cores. exact Hin. }
        rewrite go_released_eq. rewrite ack_cell_eq.
        iFrame "INV_rest". iSplitL "Hrel"; [done|].
        iExists _, b, ta0, Va0, _. iFrame "Ptsa Own". }
      iIntros "!>". iExists 0. iSplit; [done|].
      iIntros "!> !>". by iApply ("IHack" with "Hmach Hic HΦ").
    + (* read #1 — proceed *)
      destruct b; last first.
      { iDestruct "Own" as %Eqζ'. exfalso.
        rewrite Eqζ' in Sub2.
        apply (lookup_weaken _ _ _ _ Eqt'), lookup_singleton_Some in Sub2 as [].
        by apply NEqta0. }
      iClear "IHack".
      iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "Own".
      rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      have ? : t' = t1.
      { case (decide (t' = t1)) => [//|NEqt1].
        exfalso. by rewrite !lookup_insert_ne // in Sub2. }
      subst t'. rewrite lookup_insert_eq in Sub2. inversion Sub2. subst v' V'.
      iMod ("Close" with "[Hrel INV_rest Ptsa Own]").
      { iIntros "!>". rewrite /bc_inv_intc_def. iApply (big_sepS_delete _ (all_cores n) i).
        { rewrite elem_of_all_cores. exact Hin. }
        rewrite go_released_eq. rewrite ack_cell_eq.
        iFrame "INV_rest". iSplitL "Hrel"; [done|].
        iExists _, true, ta0, Va0, _. iFrame "Ptsa".
        iExists t1, V1. iSplit.
        { iPureIntro. split; [exact Lt1 | exact Eqζ']. }
        iFrame "Own". }
      iIntros "!>". iExists 1. iSplit; [done|]. iIntros "!> !>". wp_seq.
      (* core i has acked: step the machine ghost through the controller's
         send+ack, and the abstract Intc ghost in lockstep. *)
      destruct Hok as (Hipi & Hlen & Hm & Hd).
      assert (Hinz : Z.lt (Z.of_nat i) (Z.of_nat n)) by lia.
      assert (Hleni : Nat.lt i (length (intc_types.Intc_pending ic))) by (rewrite Hlen; exact HinN).
      assert (Hmi : intc.intc_get_bit (intc_types.Intc_masked ic) (Z.of_nat i) false = false)
        by (apply Hm; exact HinN).
      assert (Hdi : intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat i) false = true)
        by (apply Hd; exact HinN).
      set (ic' := intc.intc_ack (intc.intc_send ic (Z.of_nat i)) (Z.of_nat i)).
      iMod (machine_ctx_update γm (bc_machine root va mem n i)
              (receive_ipi (Machine_with_ipi (bc_machine root va mem n i)
                 (intc_types.Intc_ipi ic')) (Z.of_nat i) va)
              with "Hmach") as "Hmach'".
      iMod (intc_ctx_update γic ic ic' with "Hic") as "Hic'".
      iAssert (machine_ctx γm (bc_machine root va mem n (i + 1)%nat)) with "[Hmach']" as "Hmach''".
      { rewrite (bc_machine_ipi_step_via_intc root va mem ic n i Hinz Hipi Hleni Hmi Hdi).
        subst ic'. iFrame "Hmach'". }
      iAssert (⌜intc_step_ok ic' n (i + 1)%nat⌝)%I as "Hok'".
      { iPureIntro. subst ic'.
        apply (intc_step_ok_step ic n i HinN).
        exact (conj Hipi (conj Hlen (conj Hm Hd))). }
      wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
      iApply ("IH" $! ic' (i + 1)%nat Φ with "Hmach'' Hic' HΦ Hok'").
  - (* i ≥ n: return *)
    iMod (machine_ctx_update γm (bc_machine root va mem n i) (bc_post_machine root va mem n)
            with "Hmach") as "Hmach'".
    wp_op. rewrite bool_decide_false; [|lia]. wp_if.
    iAssert (∃ ic', intc_ctx γic ic' ∗ ⌜intc_step_ok ic' n n⌝)%I with "[Hic]" as "Hpost".
    { iExists ic. iFrame "Hic".
      iPureIntro. rewrite /intc_step_ok.
      destruct Hok as (Hipi & Hlen & Hm & Hd).
      assert (Hge : n ≤ i) by lia.
      repeat split.
      - rewrite Hipi. apply (ipi_prefix_ge n i Hge).
      - exact Hlen.
      - intros j Hjn. apply (Hm j Hjn).
      - intros j Hjn. apply (Hd j Hjn). }
    by iApply ("HΦ" with "[$Hmach' $Hpost]").
Qed.

End bc_remote_intc.

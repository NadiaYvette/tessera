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

(* The controller's delivery step (`intc.intc_ack`): read pending[i], masked[i],
   delivery[i]; if pending ∧ ¬masked ∧ delivery then clear pending[i] and ring
   the doorbell ipi[i] (release), returning 1 (delivered); else return 0 (no
   delivery).  The expression language has no `&&`/`¬` operators, so the gate is
   three nested `if:` (each `if: c then A else B` runs A iff c is nonzero). *)
Definition intc_ack_op : val :=
  λ: ["pending"; "masked"; "delivery"; "ipi"; "i"],
    let: "p" := !("pending" +ₗ "i") in
    let: "m" := !("masked" +ₗ "i") in
    let: "d" := !("delivery" +ₗ "i") in
    if: "p" then
      if: "m" then #0
      else if: "d"
           then ("pending" +ₗ "i") <- #0 ;; ("ipi" +ₗ "i") <-ʳᵉˡ #1 ;; #1
           else #0
    else #0.

(* The remote: acquire pending[i] (the IPI is sent), ack via the controller
   (delivery), acquire its doorbell ipi[i], clear its TLB, release ack[i]. *)
Definition bc_remote_intc : val :=
  λ: ["pending"; "masked"; "delivery"; "ipi"; "ack"; "tlb"; "i"],
    (repeat: !ᵃᶜ("pending" +ₗ "i")) ;;
    intc_ack_op ["pending"; "masked"; "delivery"; "ipi"; "i"] ;;
    (repeat: !ᵃᶜ("ipi" +ₗ "i")) ;;
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

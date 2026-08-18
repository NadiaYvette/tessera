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

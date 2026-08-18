(* Tessera — S2.5 (ghost bridge): the S2.4 weak-memory broadcast's per-step IPI
   transition is realized by the interrupt-controller device (SSG-3).

   S2.4 (shootdown_weak_broadcast.v) threads `Machine_ipi` through the
   N-core weak-memory broadcast: the leader's ghost step on ack i is exactly
   `receive_ipi (deliver_ipi _ (Z.of_nat i)) (Z.of_nat i) va`
   (`bc_machine_ipi_step`).  That `deliver_ipi` is a bare mailbox bit.

   SSG-3's device (intc.sail, proved in intc_proofs.v) *produces* that bit:
   `intc_send` latches the pending line, `intc_ack` rings the doorbell, and
   `intc_receive_ipi_eq_deliver` proves the controller's send+ack makes
   `receive_ipi` flush exactly as `deliver_ipi` does.

   This file composes the two: the S2.4 weak-memory ghost step is literally the
   controller's send+ack followed by `receive_ipi`.  That is the ghost-level
   "device-in-the-loop" lift — the weak-memory broadcast's IPI delivery is
   realized by the interrupt controller, not a hand-set mailbox.  (The full
   lift changes the *program* so the remote's flush is gated on the controller
   doorbell; this bridge is the pure precondition that program must satisfy.)

   See doc/stage2-shootdown.md (S2.5) and doc/system-state-goals.md (SSG-3). *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import machine_types.
Require Import machine.
Require intc.
Require intc_types.
Require Import intc_proofs.          (* intc_receive_ipi_eq_deliver, Machine_with_ipi *)
Require Import shootdown_weak_broadcast. (* bc_machine, bc_machine_ipi_step *)
Import ListNotations.

(* The leader's S2.4 ghost step, re-routed through the interrupt controller: the
   next machine [bc_machine n (i+1)] is exactly [receive_ipi] of the machine
   whose mailbox is the controller's send+ack for core i. *)
Lemma bc_machine_ipi_step_via_intc (root : mword 44) (va : mword 64) (mem : list MemEntry)
    (ic : intc_types.Intc) (n i : nat) (Hin : i < n)
    (Hag : intc_types.Intc_ipi ic = Machine_ipi (bc_machine root va mem n i))
    (Hlen : Nat.lt i (length (intc_types.Intc_pending ic)))
    (Hm : intc.intc_get_bit (intc_types.Intc_masked ic) (Z.of_nat i) false = false)
    (Hd : intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat i) false = true) :
  bc_machine root va mem n (i + 1)
  = receive_ipi
      (Machine_with_ipi (bc_machine root va mem n i)
         (intc_types.Intc_ipi (intc.intc_ack (intc.intc_send ic (Z.of_nat i)) (Z.of_nat i))))
      (Z.of_nat i) va.
Proof.
  rewrite (bc_machine_ipi_step root va mem n i Hin).
  rewrite (intc_receive_ipi_eq_deliver (bc_machine root va mem n i) ic i va Hag Hlen Hm Hd).
  reflexivity.
Qed.

(* The same bridge, phrased on what the remote observes: the flushed core is
   identical whether the IPI came from the controller or from deliver_ipi. *)
Lemma bc_machine_ipi_step_via_intc_cores (root : mword 44) (va : mword 64) (mem : list MemEntry)
    (ic : intc_types.Intc) (n i : nat) (Hin : i < n)
    (Hag : intc_types.Intc_ipi ic = Machine_ipi (bc_machine root va mem n i))
    (Hlen : Nat.lt i (length (intc_types.Intc_pending ic)))
    (Hm : intc.intc_get_bit (intc_types.Intc_masked ic) (Z.of_nat i) false = false)
    (Hd : intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat i) false = true) :
  Machine_cores (bc_machine root va mem n (i + 1))
  = Machine_cores
      (receive_ipi
         (Machine_with_ipi (bc_machine root va mem n i)
            (intc_types.Intc_ipi (intc.intc_ack (intc.intc_send ic (Z.of_nat i)) (Z.of_nat i))))
         (Z.of_nat i) va).
Proof.
  rewrite (bc_machine_ipi_step_via_intc root va mem ic n i Hin Hag Hlen Hm Hd).
  reflexivity.
Qed.

(* Tessera — Stage 2, S2.3 (SSG-3): IPI delivery and "delivery precedes ack".

   The shootdown so far is a functional broadcast (`map sfence_vma_va` over the
   cores); there is no IPI-delivery transition.  machine.sail now carries a
   per-core IPI mailbox (`Machine.ipi`, parallel to `Machine.cores`) and two
   transitions: `deliver_ipi m i` (the leader marks core i's IPI delivered) and
   `receive_ipi m i va` (core i flushes `va` from its TLB — but only if its IPI
   has been delivered).  This file proves the crux of SSG-3: a remote cannot ack
   (flush) before delivery, and once delivered, the ack flushes the right core.

   The pure-model form of "delivery precedes ack" is `receive_ipi`'s guard:
     - `receive_ipi_before_delivery_noop`  — undelivered ⇒ `receive_ipi` is a no-op.
     - `receive_ipi_after_delivery_sfences` — delivered ⇒ the i-th core is flushed.

   See ../../doc/system-state-goals.md (SSG-3) and ../../doc/stage2-shootdown.md
   (S2.3). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import machine_types.
Require Import machine.
Import ListNotations.

(* ============================================================
   The IPI transitions, restated over a natural-number index.

   The generated `deliver_ipi`/`receive_ipi`/`receive_ipi_cores`/`list_nth_bool`/
   `list_update_bool` take a `Z` index (Sail `int`).  The proofs below index cores
   with `nat` and convert via `Z.of_nat`.
   ============================================================ *)

(* `receive_ipi_cores` with `delivered = false` is the identity: no flush.  This
   is the "no ack before delivery" half of the guard. *)
Lemma receive_ipi_cores_false (cores : list Core) (i : Z) (va : mword 64) :
  receive_ipi_cores cores i false va = cores.
Proof.
  revert i. induction cores as [| c cs IH]; intros i; cbn [receive_ipi_cores].
  - reflexivity.
  - destruct (Z.eqb i 0) eqn:E; cbn; [reflexivity | f_equal; apply IH].
Qed.

(* `list_update_bool` then `list_nth_bool` at the same (in-range) index returns
   the new value: `deliver_ipi` really does set the delivered bit. *)
Lemma list_nth_bool_update_self (l : list bool) (i : nat) :
  Nat.lt i (length l) ->
  list_nth_bool (list_update_bool l (Z.of_nat i) true) (Z.of_nat i) false = true.
Proof.
  revert i. induction l as [| b bs IH]; intros [| i] H; cbn [list_update_bool list_nth_bool length].
  - simpl in H. lia.
  - simpl in H. lia.
  - cbn. reflexivity.
  - cbn [length] in H.
    destruct (Z.eqb (Z.of_nat (S i)) 0) eqn:E.
    + apply Z.eqb_eq in E. lia.
    + cbn [list_update_bool list_nth_bool].
      rewrite E. cbn [list_nth_bool].
      replace (Z.sub (Z.of_nat (S i)) 1) with (Z.of_nat i) by lia.
      apply IH. lia.
Qed.

(* A helper: sfence position `i` of the core list. *)
Fixpoint sfence_at (cores : list Core) (i : nat) (va : mword 64) : list Core :=
  match cores, i with
  | c :: cs, O   => sfence_vma_va c va :: cs
  | c :: cs, S k => c :: sfence_at cs k va
  | [], _        => []
  end.

(* `receive_ipi_cores` with `delivered = true` sfences position `i` (as a nat). *)
Lemma receive_ipi_cores_true_eq_sfence_at (cores : list Core) (i : nat) (va : mword 64) :
  receive_ipi_cores cores (Z.of_nat i) true va = sfence_at cores i va.
Proof.
  revert i. induction cores as [| c cs IH]; intros [| i]; cbn [receive_ipi_cores sfence_at].
  - reflexivity.
  - reflexivity.
  - cbn. reflexivity.
  - destruct (Z.eqb (Z.of_nat (S i)) 0) eqn:E.
    + apply Z.eqb_eq in E. lia.
    + cbn [receive_ipi_cores].
      f_equal.
      replace (Z.sub (Z.of_nat (S i)) 1) with (Z.of_nat i) by lia.
      apply IH.
Qed.

(* sfence-ing position i reads back the sfenced core at position i. *)
Lemma sfence_at_nth_self (cores : list Core) (i : nat) (va : mword 64) :
  nth_error (sfence_at cores i va) i =
  option_map (fun c => sfence_vma_va c va) (nth_error cores i).
Proof.
  revert i. induction cores as [| c cs IH]; intros [| i]; cbn [sfence_at nth_error].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply IH.
Qed.

(* ============================================================
   The machine-level "delivery precedes ack" statements.
   ============================================================ *)

(* Undelivered ⇒ receive_ipi is a no-op: a remote cannot flush (ack) before its
   IPI is delivered. *)
Lemma receive_ipi_before_delivery_noop (m : Machine) (i : Z) (va : mword 64) :
  list_nth_bool m.(Machine_ipi) i false = false ->
  receive_ipi m i va = m.
Proof.
  intros H. unfold receive_ipi.
  rewrite H.
  rewrite receive_ipi_cores_false.
  destruct m; cbn. reflexivity.
Qed.

(* Delivered ⇒ receive_ipi flushes core i's TLB (the ack happens after
   delivery). *)
Lemma receive_ipi_after_delivery_sfences (m : Machine) (i : nat) (va : mword 64) :
  Nat.lt i (length m.(Machine_cores)) ->
  Nat.lt i (length m.(Machine_ipi)) ->
  nth_error (receive_ipi (deliver_ipi m (Z.of_nat i)) (Z.of_nat i) va).(Machine_cores) i =
  option_map (fun c => sfence_vma_va c va) (nth_error m.(Machine_cores) i).
Proof.
  intros Hcore Hipi.
  unfold receive_ipi, deliver_ipi.
  cbn [Machine_cores Machine_ipi].
  rewrite list_nth_bool_update_self by exact Hipi.
  rewrite receive_ipi_cores_true_eq_sfence_at.
  apply sfence_at_nth_self.
Qed.

(* `deliver_ipi` only touches the mailbox, leaving cores/mem/ram unchanged. *)
Lemma deliver_ipi_preserves_cores (m : Machine) (i : Z) :
  (deliver_ipi m i).(Machine_cores) = m.(Machine_cores).
Proof. reflexivity. Qed.

(* `receive_ipi` only touches the cores, leaving mem/ram/ipi unchanged. *)
Lemma receive_ipi_preserves_mem (m : Machine) (i : Z) (va : mword 64) :
  (receive_ipi m i va).(Machine_mem) = m.(Machine_mem).
Proof. reflexivity. Qed.

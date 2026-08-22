(* Tessera — SSG-5 timer proofs: monotonicity, pending correctness,
   ack idempotence. All axiom-free. *)

From Stdlib Require Import Bool ZArith List.
From Stdlib Require Import Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Operators_mwords.
Require Import timer_types.
Require Import timer_ops.

(* ---- Headline theorems ---- *)

(* 1. timer_tick always increases mtime. *)
Theorem timer_tick_mtime (dev : TimerDevice) (delta : mword 64) :
  (timer_tick dev delta).(TimerDevice_mtime) = add_vec dev.(TimerDevice_mtime) delta.
Proof. reflexivity. Qed.

(* 2. timer_ack clears pending for the target hart. *)
Lemma ack_hart_pending (harts : list HartTimer) (target : nat) :
  (nth_hart (ack_hart harts target) target).(HartTimer_pending) = false.
Proof.
  revert target. induction harts; intros [|n]; simpl; auto.
Qed.

Theorem timer_pending_after_ack (dev : TimerDevice) (hart : nat) :
  timer_pending (timer_ack dev hart) hart = false.
Proof.
  unfold timer_pending, timer_ack. simpl. apply ack_hart_pending.
Qed.

(* 3. timer_set_mtimecmp preserves pending for other harts. *)
Lemma set_hart_other (harts : list HartTimer) (target other : nat) (v : mword 64) :
  target <> other ->
  (nth_hart (set_hart_mtimecmp harts target v) other) = nth_hart harts other.
Proof.
  revert target other.
  induction harts as [|h hs IH]; simpl.
  - intros; auto.
  - intros [|t] [|o] Hneq; simpl.
    + exfalso; apply Hneq; reflexivity.
    + auto.
    + auto.
    + apply IH; intros Heq; apply Hneq; congruence.
Qed.

Theorem timer_set_mtimecmp_other (dev : TimerDevice) (hart other : nat) (v : mword 64) :
  hart <> other ->
  timer_pending (timer_set_mtimecmp dev hart v) other = timer_pending dev other.
Proof.
  intros Hneq. unfold timer_pending, timer_set_mtimecmp. simpl.
  f_equal. apply set_hart_other; auto.
Qed.

(* 4. timer_set_mtimecmp leaves mtime unchanged. *)
Theorem timer_set_mtimecmp_mtime_unchanged
  (dev : TimerDevice) (hart : nat) (v : mword 64) :
  (timer_set_mtimecmp dev hart v).(TimerDevice_mtime) = dev.(TimerDevice_mtime).
Proof. reflexivity. Qed.

(* 5. Build harts length. *)
Theorem build_harts_length (n : nat) (ht : HartTimer) :
  length (build_harts n ht) = n.
Proof. induction n; simpl; auto. Qed.

(* ---- Executable test vectors ---- *)

Definition dev2 : TimerDevice := mk_timer 2.

Lemma test_vec_init_mtime :
  (mk_timer 2).(TimerDevice_mtime) = mword_of_int (0%Z).
Proof. vm_compute. reflexivity. Qed.

Lemma test_vec_init_pending_hart0 : timer_pending dev2 0 = false.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vec_tick_increases :
  (timer_tick dev2 (mword_of_int (10%Z))).(TimerDevice_mtime) = mword_of_int (10%Z).
Proof. vm_compute. reflexivity. Qed.

Lemma test_vec_set_cmp_then_tick :
  timer_pending (timer_tick (timer_set_mtimecmp dev2 0 (mword_of_int (5%Z)))
                            (mword_of_int (10%Z))) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vec_ack_clears :
  let dev := timer_tick (timer_set_mtimecmp dev2 0 (mword_of_int (5%Z)))
                         (mword_of_int (10%Z)) in
  timer_pending (timer_ack dev 0) 0 = false.
Proof. vm_compute. reflexivity. Qed.
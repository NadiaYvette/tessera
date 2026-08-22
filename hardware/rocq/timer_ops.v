(* Tessera — the timer device (SSG-5): per-hart mtimecmp, monotonic
   mtime counter, timer-interrupt pending bits.

   timer_types.v (generated from timer.sail by sail --rocq) provides
   HartTimer and TimerDevice records.  This file hand-writes the operations
   to avoid Sail's Z-recursion termination issues.  All functions pure. *)

From Stdlib Require Import Bool ZArith List.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import timer_types.
Import ListNotations.

(* Unsigned comparison: mtime >= mtimecmp. *)
Definition timer_compare (mtime mtimecmp : mword 64) : bool :=
  Z.geb (int_of_mword false mtime) (int_of_mword false mtimecmp).

(* nth_hart with a default sentinel.  id : nat for structural recursion. *)
Fixpoint nth_hart (harts : list HartTimer) (id : nat) : HartTimer :=
  match harts, id with
  | [], _ =>
      {| HartTimer_mtimecmp := mword_of_int (0%Z); HartTimer_pending := false |}
  | h :: _, 0%nat => h
  | _ :: hs, S n => nth_hart hs n
  end.

Definition timer_pending (dev : TimerDevice) (hart : nat) : bool :=
  (nth_hart dev.(TimerDevice_harts) hart).(HartTimer_pending).

(* Update pending bits: for each hart, set pending when mtime >= mtimecmp. *)
Fixpoint tick_harts (harts : list HartTimer) (mtime : mword 64) : list HartTimer :=
  match harts with
  | [] => []
  | h :: hs =>
      let h' := {| HartTimer_mtimecmp := h.(HartTimer_mtimecmp);
                   HartTimer_pending := orb h.(HartTimer_pending)
                       (timer_compare mtime h.(HartTimer_mtimecmp)) |} in
      h' :: tick_harts hs mtime
  end.

(* Set mtimecmp for hart at index target. *)
Fixpoint set_hart_mtimecmp (harts : list HartTimer) (target : nat) (newval : mword 64)
  : list HartTimer :=
  match harts, target with
  | [], _ => []
  | h :: hs, 0%nat =>
      {| HartTimer_mtimecmp := newval; HartTimer_pending := h.(HartTimer_pending) |} :: hs
  | h :: hs, S n => h :: set_hart_mtimecmp hs n newval
  end.

(* Clear pending for hart at index target. *)
Fixpoint ack_hart (harts : list HartTimer) (target : nat) : list HartTimer :=
  match harts, target with
  | [], _ => []
  | h :: hs, 0%nat =>
      {| HartTimer_mtimecmp := h.(HartTimer_mtimecmp); HartTimer_pending := false |} :: hs
  | h :: hs, S n => h :: ack_hart hs n
  end.

(* Build n copies of the default HartTimer. *)
Fixpoint build_harts (n : nat) (ht : HartTimer) : list HartTimer :=
  match n with
  | 0%nat => []
  | S n' => ht :: build_harts n' ht
  end.

(* ---- device transitions ---- *)

Definition read_mtime (dev : TimerDevice) : mword 64 := dev.(TimerDevice_mtime).

Definition timer_tick (dev : TimerDevice) (delta : mword 64) : TimerDevice :=
  let new_mtime := add_vec dev.(TimerDevice_mtime) delta in
  {| TimerDevice_mtime := new_mtime;
     TimerDevice_harts := tick_harts dev.(TimerDevice_harts) new_mtime |}.

Definition timer_set_mtimecmp (dev : TimerDevice) (hart : nat) (newval : mword 64)
  : TimerDevice :=
  {| TimerDevice_mtime := dev.(TimerDevice_mtime);
     TimerDevice_harts := set_hart_mtimecmp dev.(TimerDevice_harts) hart newval |}.

Definition timer_ack (dev : TimerDevice) (hart : nat) : TimerDevice :=
  {| TimerDevice_mtime := dev.(TimerDevice_mtime);
     TimerDevice_harts := ack_hart dev.(TimerDevice_harts) hart |}.

(* Initial state: n harts, mtime = 0, mtimecmp = max, pending = false. *)
Definition default_hart : HartTimer :=
  {| HartTimer_mtimecmp := mword_of_int (0xFFFFFFFFFFFFFFFF%Z);
     HartTimer_pending := false |}.

Definition mk_timer (n : nat) : TimerDevice :=
  {| TimerDevice_mtime := mword_of_int (0%Z);
     TimerDevice_harts := build_harts n default_hart |}.
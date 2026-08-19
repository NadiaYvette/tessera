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

   S2.3b (below) composes the per-core transitions into the full broadcast
   (`ipi_broadcast`): the leader invalidates the leaf PTE, delivers the IPI to,
   and receives the ack from, every core — and `ipi_broadcast_correct` proves the
   result refines the functional `invalidate_shootdown` (same mem, same flushed
   cores), hence re-establishes the same coherence on every core.

   See ../../doc/system-state-goals.md (SSG-3) and ../../doc/stage2-shootdown.md
   (S2.3). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import machine_types.
Require Import machine.
Require Import coherence_leaf.  (* invalidate_leaf_mem *)
Require Import shootdown.       (* core_with_root, invalidate_shootdown, invalidate_shootdown_correct *)
Require Import machine_encoding. (* leaf_entry, invalid_pte *)
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

(* ============================================================
   S2.3b: the composed IPI broadcast, refining `invalidate_shootdown`.
   ============================================================ *)

(* Flush the first n cores' TLBs (a prefix-map of sfence_vma_va).  Structurally
   recursive on n (`{struct n}`) so `sfence_prefix cores 0` reduces to `cores`
   even when `cores` is a variable — the automatic `{struct cores}` inference
   would otherwise leave it stuck. *)
Fixpoint sfence_prefix (cores : list Core) (n : nat) (va : mword 64) {struct n} : list Core :=
  match n with
  | O => cores
  | S k =>
      match cores with
      | c :: cs => sfence_vma_va c va :: sfence_prefix cs k va
      | [] => []
      end
  end.

(* sfence_prefix preserves the list length (when n is in range). *)
Lemma length_sfence_prefix (cores : list Core) (n : nat) (va : mword 64) :
  Nat.le n (length cores) ->
  length (sfence_prefix cores n va) = length cores.
Proof.
  revert n. induction cores as [| c cs IH]; intros [| n] H; cbn [sfence_prefix length].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IH. cbn in H. lia.
Qed.

(* Flushing the whole list is exactly the full map. *)
Lemma sfence_prefix_full (cores : list Core) (va : mword 64) :
  sfence_prefix cores (length cores) va = List.map (fun c => sfence_vma_va c va) cores.
Proof.
  induction cores as [| c cs IH]; cbn [sfence_prefix length List.map].
  - reflexivity.
  - f_equal. exact IH.
Qed.

(* `list_update_bool` preserves the list length. *)
Lemma list_update_bool_length (l : list bool) (i : Z) (v : bool) :
  length (list_update_bool l i v) = length l.
Proof.
  revert i. induction l as [| b bs IH]; intros i; cbn [list_update_bool length].
  - reflexivity.
  - destruct (Z.eqb i 0); cbn; [reflexivity | f_equal; apply IH].
Qed.

(* Once delivered, receive_ipi flushes exactly core i — as a full-list equality
   (the strengthened form of `receive_ipi_after_delivery_sfences`). *)
Lemma receive_ipi_after_delivery_cores (m : Machine) (i : nat) (va : mword 64) :
  Nat.lt i (length m.(Machine_cores)) ->
  Nat.lt i (length m.(Machine_ipi)) ->
  (receive_ipi (deliver_ipi m (Z.of_nat i)) (Z.of_nat i) va).(Machine_cores) =
  sfence_at m.(Machine_cores) i va.
Proof.
  intros Hcore Hipi.
  unfold receive_ipi, deliver_ipi.
  cbn [Machine_cores Machine_ipi].
  rewrite list_nth_bool_update_self by exact Hipi.
  rewrite receive_ipi_cores_true_eq_sfence_at.
  reflexivity.
Qed.

(* sfence-ing position k of the k-prefix extends the prefix by one. *)
Lemma sfence_at_prefix_S (cores : list Core) (k : nat) (va : mword 64) :
  Nat.lt k (length cores) ->
  sfence_at (sfence_prefix cores k va) k va = sfence_prefix cores (S k) va.
Proof.
  revert k. induction cores as [| c cs IH]; intros [| k] H.
  - cbn [sfence_at sfence_prefix]. reflexivity.
  - cbn [sfence_at sfence_prefix]. reflexivity.
  - cbn [sfence_at sfence_prefix]. reflexivity.
  - cbn [sfence_at sfence_prefix]. f_equal. apply IH. cbn in H. lia.
Qed.

(* The broadcast loop: deliver the IPI to, and receive the ack from, cores
   0..n-1 in order.  mem/ram are untouched and the ipi mailbox length is
   preserved (its bits are set, but the length is what the indices need). *)
Fixpoint ipi_broadcast_cores (m : Machine) (n : nat) (va : mword 64) : Machine :=
  match n with
  | O => m
  | S k => receive_ipi (deliver_ipi (ipi_broadcast_cores m k va) (Z.of_nat k)) (Z.of_nat k) va
  end.

Lemma ipi_broadcast_cores_preserves (m : Machine) (n : nat) (va : mword 64) :
  (ipi_broadcast_cores m n va).(Machine_mem) = m.(Machine_mem) /\
  (ipi_broadcast_cores m n va).(Machine_ram) = m.(Machine_ram) /\
  length (ipi_broadcast_cores m n va).(Machine_ipi) = length m.(Machine_ipi).
Proof.
  induction n as [| k IH]; cbn [ipi_broadcast_cores].
  - auto.
  - destruct IH as [IHmem [IHram IHlen]].
    repeat split.
    + unfold receive_ipi, deliver_ipi. cbn [Machine_mem]. exact IHmem.
    + unfold receive_ipi, deliver_ipi. cbn [Machine_ram]. exact IHram.
    + unfold receive_ipi, deliver_ipi. cbn [Machine_ipi].
      rewrite list_update_bool_length. exact IHlen.
Qed.

(* After n deliver+receive steps, cores 0..n-1 are flushed (and the rest are
   untouched): the loop is exactly `sfence_prefix`. *)
Lemma ipi_broadcast_cores_spec (m : Machine) (n : nat) (va : mword 64) :
  Nat.le n (length m.(Machine_cores)) ->
  Nat.le n (length m.(Machine_ipi)) ->
  (ipi_broadcast_cores m n va).(Machine_cores) = sfence_prefix m.(Machine_cores) n va.
Proof.
  revert m. induction n as [| k IH]; intros m Hc Hipi.
  - cbn [ipi_broadcast_cores sfence_prefix]. reflexivity.
  - cbn [ipi_broadcast_cores].
    assert (Hc' : Nat.le k (length m.(Machine_cores))) by lia.
    assert (Hipi' : Nat.le k (length m.(Machine_ipi))) by lia.
    specialize (IH m Hc' Hipi').
    set (M' := ipi_broadcast_cores m k va).
    assert (HM' : M'.(Machine_cores) = sfence_prefix m.(Machine_cores) k va).
    { subst M'. exact IH. }
    assert (Hlencores : length M'.(Machine_cores) = length m.(Machine_cores)).
    { subst M'. rewrite IH. apply length_sfence_prefix. exact Hc'. }
    assert (Hlenipi : length M'.(Machine_ipi) = length m.(Machine_ipi)).
    { subst M'. destruct (ipi_broadcast_cores_preserves m k va) as [_ [_ Hl]]. exact Hl. }
    assert (Hlenc : Nat.lt k (length M'.(Machine_cores))).
    { rewrite Hlencores. lia. }
    assert (Hleni : Nat.lt k (length M'.(Machine_ipi))).
    { rewrite Hlenipi. lia. }
    rewrite (receive_ipi_after_delivery_cores M' k va Hlenc Hleni).
    rewrite HM'.
    apply sfence_at_prefix_S. lia.
Qed.

(* The full IPI-based broadcast: the leader invalidates the leaf PTE for `va`,
   then delivers the IPI to, and receives the ack from, every core (including
   the leader, whose own flush is modeled as delivering+receiving its own IPI). *)
Definition ipi_broadcast (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) : Machine :=
  let m1 := {| Machine_mem := invalidate_leaf_mem (core_with_root root) m.(Machine_mem) va p;
               Machine_cores := m.(Machine_cores);
               Machine_ram := m.(Machine_ram);
               Machine_ipi := m.(Machine_ipi);
               Machine_iotlb := m.(Machine_iotlb); Machine_devtlbs := m.(Machine_devtlbs); Machine_prireqs := m.(Machine_prireqs); Machine_ioqueue := m.(Machine_ioqueue); Machine_stes := m.(Machine_stes); Machine_cds := m.(Machine_cds) |} in
  ipi_broadcast_cores m1 (length m.(Machine_cores)) va.

(* The composed broadcast refines the functional `invalidate_shootdown`: same
   memory, same (fully-flushed) cores.  (The ipi mailbox differs — the broadcast
   sets the delivered bits — but that is internal state, not observable.) *)
Theorem ipi_broadcast_refines_invalidate_shootdown
    (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  length m.(Machine_ipi) = length m.(Machine_cores) ->
  (ipi_broadcast m root va p).(Machine_mem) = (invalidate_shootdown m root va p).(Machine_mem) /\
  (ipi_broadcast m root va p).(Machine_cores) = (invalidate_shootdown m root va p).(Machine_cores).
Proof.
  intros Hlen.
  unfold ipi_broadcast.
  set (n := length m.(Machine_cores)).
  set (m1 := {| Machine_mem := invalidate_leaf_mem (core_with_root root) m.(Machine_mem) va p;
                Machine_cores := m.(Machine_cores);
                Machine_ram := m.(Machine_ram);
                Machine_ipi := m.(Machine_ipi);
                Machine_iotlb := m.(Machine_iotlb); Machine_devtlbs := m.(Machine_devtlbs); Machine_prireqs := m.(Machine_prireqs); Machine_ioqueue := m.(Machine_ioqueue); Machine_stes := m.(Machine_stes); Machine_cds := m.(Machine_cds) |}).
  split.
  - (* mem *)
    destruct (ipi_broadcast_cores_preserves m1 n va) as [Hmem _].
    rewrite Hmem. subst m1 n. cbn.
    unfold invalidate_shootdown. cbn. reflexivity.
  - (* cores *)
    assert (Hcores_bound : Nat.le n (length m1.(Machine_cores))).
    { subst m1 n. cbn. lia. }
    assert (Hipi_bound : Nat.le n (length m1.(Machine_ipi))).
    { subst m1 n. cbn. rewrite Hlen. lia. }
    rewrite (ipi_broadcast_cores_spec m1 n va Hcores_bound Hipi_bound).
    subst m1 n. cbn.
    rewrite sfence_prefix_full.
    unfold invalidate_shootdown. cbn. reflexivity.
Qed.

(* The headline: the IPI-based broadcast re-establishes the same coherence as the
   functional `invalidate_shootdown` — no core translates the freed frame. *)
Theorem ipi_broadcast_correct (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  p.(Pte_valid) = false ->
  length m.(Machine_ipi) = length m.(Machine_cores) ->
  Forall (fun c => c.(Core_satp_ppn) = root) m.(Machine_cores) ->
  Forall (fun c => translate c (ipi_broadcast m root va p).(Machine_mem) va = None /\
                   tlb_lookup c va = None)
         (ipi_broadcast m root va p).(Machine_cores).
Proof.
  intros Hinv Hlen Hroot.
  destruct (ipi_broadcast_refines_invalidate_shootdown m root va p Hlen) as [Hmem Hcores].
  rewrite Hmem. rewrite Hcores.
  apply invalidate_shootdown_correct; assumption.
Qed.

(* ============================================================
   IPI test vectors (executable): a concrete 3-core machine and
   `vm_compute` pins for deliver_ipi / receive_ipi / ipi_broadcast.
   ============================================================ *)

Definition ipi_va : mword 64 := mword_of_int 0.
Definition ipi_root : mword 44 := mword_of_int 1.

(* A core caching the stale [leaf_entry ipi_va] for [ipi_root]. *)
Definition ipi_stale_core : Core :=
  {| Core_satp_ppn := ipi_root; Core_tlb := [leaf_entry ipi_va]; Core_hart := 0; Core_node := 0 |}.

(* A core with an empty TLB (the post-flush state). *)
Definition ipi_flushed_core : Core :=
  {| Core_satp_ppn := ipi_root; Core_tlb := []; Core_hart := 0; Core_node := 0 |}.

(* Three cores, all stale, no IPI delivered, empty mem/ram. *)
Definition ipi_machine : Machine :=
  {| Machine_cores := [ipi_stale_core; ipi_stale_core; ipi_stale_core];
     Machine_mem := [];
     Machine_ram := [];
     Machine_ipi := [false; false; false];
     Machine_iotlb := []; Machine_devtlbs := []; Machine_prireqs := []; Machine_ioqueue := []; Machine_stes := []; Machine_cds := [] |}.

(* 1. deliver_ipi sets exactly the addressed delivered bit. *)
Lemma test_vector_deliver_ipi :
  (deliver_ipi ipi_machine 1).(Machine_ipi) = [false; true; false].
Proof. vm_compute. reflexivity. Qed.

(* 2. receive_ipi before delivery is a no-op (no flush). *)
Lemma test_vector_receive_before_delivery :
  (receive_ipi ipi_machine 1 ipi_va).(Machine_cores) = ipi_machine.(Machine_cores).
Proof. vm_compute. reflexivity. Qed.

(* 3. receive_ipi after delivery flushes exactly core 1. *)
Lemma test_vector_receive_after_delivery :
  (receive_ipi (deliver_ipi ipi_machine 1) 1 ipi_va).(Machine_cores)
  = [ipi_stale_core; ipi_flushed_core; ipi_stale_core].
Proof. vm_compute. reflexivity. Qed.

(* 4. ipi_broadcast flushes every core and delivers every IPI. *)
Lemma test_vector_ipi_broadcast :
  let m' := ipi_broadcast ipi_machine ipi_root ipi_va invalid_pte in
  m'.(Machine_ipi) = [true; true; true] /\
  m'.(Machine_cores) = [ipi_flushed_core; ipi_flushed_core; ipi_flushed_core].
Proof. vm_compute. split; reflexivity. Qed.

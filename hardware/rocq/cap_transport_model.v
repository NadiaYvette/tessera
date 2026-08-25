(* Tessera — K1.5, Layer A: pure Coq model of the capability transport.

   This is the *abstract specification* the Iris heap_lang spec
   (cap_transport_iris.v, pending K1) will state, proven here first in
   plain Coq — the same Layer-A-before-machine pattern as the Lean
   `proof/` work.  It mirrors the kernel-v2 Rust (Telix
   `kernel-v2/src/caps/`) function for function:

     caps/table.rs      ->  alloc_slot / free_slot / grant
     caps/port.rs       ->  port_send / port_recv
     caps/transport.rs  ->  has_port_cap / gated_send  (cap-gated send)

   Theorems (all axiom-free, checked by build.sh):
     - send_never_drops       : port_send on a full port errors (None),
                                on a non-full port appends.
     - recv_fifo              : two sends from an empty queue, then two
                                recvs, return the messages in order.
     - grant_no_amplification : grant with non-subset rights errors;
                                grant copies with the subset rights.
     - cap_unforgeable        : a task whose table lacks the port cap
                                with the needed right cannot send.
     - no_partial_mutation    : failing ops leave the state unchanged
                                (pure functions; the lemmas state the
                                failure conditions).

   See doc/k1-minimal-subset.md for the machine-interface contract this
   model feeds. *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

(* ================================================================== *)
(* 1. Rights: a five-bit lattice with boolean subset test.            *)
(* ================================================================== *)

Record rights : Set := mk_rights {
  r_read  : bool;
  r_write : bool;
  r_grant : bool;
  r_send  : bool;
  r_recv  : bool;
}.

Definition bimpl (a b : bool) : bool := negb a || b.

Definition r_subsetb (r1 r2 : rights) : bool :=
  bimpl (r_read r1)  (r_read r2)  &&
  bimpl (r_write r1) (r_write r2) &&
  bimpl (r_grant r1) (r_grant r2) &&
  bimpl (r_send r1)  (r_send r2)  &&
  bimpl (r_recv r1)  (r_recv r2).

Lemma negb_orb_self (a : bool) : negb a || a = true.
Proof. destruct a; reflexivity. Qed.

Lemma r_subsetb_refl (r : rights) : r_subsetb r r = true.
Proof.
  unfold r_subsetb, bimpl. destruct r; simpl; rewrite ?negb_orb_self; reflexivity.
Qed.

Lemma bimpl_true (a b : bool) : bimpl a b = true -> a = true -> b = true.
Proof. unfold bimpl. intros H Ha. destruct a, b; simpl in *; auto. Qed.

Lemma r_subsetb_true_send (r1 r2 : rights) :
  r_subsetb r1 r2 = true -> r_send r1 = true -> r_send r2 = true.
Proof.
  destruct r1 as [a1 b1 c1 d1 e1]; destruct r2 as [a2 b2 c2 d2 e2]; simpl.
  intros H Hs.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ Hsend].
  apply (bimpl_true _ _ Hsend); exact Hs.
Qed.

Lemma r_subsetb_true_recv (r1 r2 : rights) :
  r_subsetb r1 r2 = true -> r_recv r1 = true -> r_recv r2 = true.
Proof.
  destruct r1 as [a1 b1 c1 d1 e1]; destruct r2 as [a2 b2 c2 d2 e2]; simpl.
  intros H Hr.
  apply andb_true_iff in H as [_ Hrecv].
  apply (bimpl_true _ _ Hrecv); exact Hr.
Qed.

(* ================================================================== *)
(* 2. Capabilities and the capability table.                          *)
(* ================================================================== *)

Inductive cap_type : Set :=
  | CPort (pid : nat)
  | CMem (base : nat) (pages : nat).

Record cap_slot : Set := mk_cap_slot {
  slot_ty     : cap_type;
  slot_rights : rights;
}.

Definition table : Set := list (option cap_slot).

(* The first empty slot (None) in a table, if any. *)
Fixpoint first_free (t : table) : option nat :=
  match t with
  | nil => None
  | None :: _ => Some 0
  | Some _ :: tl => option_map S (first_free tl)
  end.

(* Replace the i-th element; out-of-range leaves the list unchanged. *)
Fixpoint replace_nth (i : nat) (t : table) (v : option cap_slot) : table :=
  match t, i with
  | nil, _ => nil
  | _ :: tl, 0 => v :: tl
  | h :: tl, S j => h :: replace_nth j tl v
  end.

Lemma length_replace_nth (i : nat) (t : table) (v : option cap_slot) :
  length (replace_nth i t v) = length t.
Proof. revert i. induction t; intros i; destruct i; simpl; auto. Qed.

Lemma nth_error_replace_nth_same (i : nat) (t : table) (v : option cap_slot)
  (Hin : i < length t) :
  nth_error (replace_nth i t v) i = Some v.
Proof.
  revert i Hin. induction t as [| a tl IHt]; intros i Hin; simpl in Hin.
  - lia.
  - destruct i as [| i']; [ reflexivity | ].
    simpl. apply Nat.lt_succ_lt_pred in Hin. simpl in Hin.
    apply IHt. exact Hin.
Qed.

Lemma nth_error_replace_nth_other (i j : nat) (t : table) (v : option cap_slot)
  (Hneq : i <> j) :
  nth_error (replace_nth i t v) j = nth_error t j.
Proof.
  revert i j Hneq. induction t as [| a tl IHt]; intros i j Hneq.
  - simpl. destruct i, j; reflexivity.
  - destruct i as [| i']; destruct j as [| j']; simpl; try reflexivity; try congruence.
    apply IHt. intros H. apply Hneq. exact (f_equal S H).
Qed.

(* Soundness of first_free: it points at an empty slot. *)
Lemma first_free_some_sound (t : table) (i : nat) :
  first_free t = Some i -> nth_error t i = Some None.
Proof.
  revert i. induction t as [| a tl IHt]; intros i H; simpl in H.
  - discriminate.
  - destruct a as [s |]; simpl in H.
    + destruct (first_free tl) as [j |] eqn:E; simpl in H; [| discriminate].
      destruct i as [| i']; simpl in H; [ discriminate H | ].
      injection H as Hj. subst j. apply IHt. reflexivity.
    + destruct i as [| i']; [ reflexivity | discriminate ].
Qed.

(* first_free Some i implies i is in range. *)
Lemma first_free_some_in_range (t : table) (i : nat) :
  first_free t = Some i -> i < length t.
Proof.
  revert i. induction t as [| a tl IHt]; intros i H; simpl in H.
  - discriminate.
  - destruct a as [s |]; simpl in H.
    + destruct (first_free tl) as [j |] eqn:E; simpl in H; [| discriminate].
      destruct i as [| i']; simpl in H; [ simpl; lia | ].
      injection H as Hj. subst j.
      assert (Hi' : i' < length tl) by (apply IHt; reflexivity).
      simpl. lia.
    + destruct i as [| i']; [ simpl; lia | discriminate H ].
Qed.

(* ------------------------------------------------------------------ *)
(* alloc_slot: fill the first free slot.                              *)
(* ------------------------------------------------------------------ *)

Definition alloc_slot (t : table) (ty : cap_type) (r : rights) :
  option (nat * table) :=
  match first_free t with
  | Some i => Some (i, replace_nth i t (Some (mk_cap_slot ty r)))
  | None => None
  end.

Lemma alloc_slot_fills_slot (t : table) (ty : cap_type) (r : rights)
  (i : nat) (t' : table) (H : alloc_slot t ty r = Some (i, t')) :
  nth_error t i = Some None /\
  nth_error t' i = Some (Some (mk_cap_slot ty r)) /\
  length t' = length t.
Proof.
  unfold alloc_slot in H.
  destruct (first_free t) as [j |] eqn:E; [| discriminate].
  injection H as H; subst.
  split; [ apply first_free_some_sound; exact E | ].
  split.
  - apply nth_error_replace_nth_same.
    apply first_free_some_in_range with (t := t). exact E.
  - apply length_replace_nth.
Qed.

Lemma alloc_slot_preserves_others (t : table) (ty : cap_type) (r : rights)
  (i j : nat) (t' : table) (H : alloc_slot t ty r = Some (i, t'))
  (Hneq : i <> j) :
  nth_error t' j = nth_error t j.
Proof.
  unfold alloc_slot in H.
  destruct (first_free t) as [k |] eqn:E; [| discriminate].
  injection H as H; subst.
  apply nth_error_replace_nth_other. exact Hneq.
Qed.

(* alloc_slot on a full table returns None (state unchanged, trivially). *)
Lemma alloc_slot_full_none (t : table) (ty : cap_type) (r : rights) :
  (forall i, i < length t -> exists s : cap_slot, nth_error t i = Some (Some s)) ->
  alloc_slot t ty r = None.
Proof.
  intros Hfull. unfold alloc_slot.
  destruct (first_free t) as [i |] eqn:E; [| reflexivity].
  assert (Hin : i < length t) by (apply first_free_some_in_range with (t := t); exact E).
  apply first_free_some_sound in E.
  destruct (Hfull i) as [s Hs]; [ exact Hin | ].
  rewrite E in Hs. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* free_slot: invalidate the i-th slot.                               *)
(* ------------------------------------------------------------------ *)

Definition free_slot (t : table) (i : nat) : option (cap_slot * table) :=
  match nth_error t i with
  | Some (Some s) => Some (s, replace_nth i t None)
  | _ => None
  end.

Lemma free_slot_invalidates (t : table) (i : nat) (s : cap_slot) (t' : table)
  (H : free_slot t i = Some (s, t')) :
  nth_error t i = Some (Some s) /\ nth_error t' i = Some None.
Proof.
  unfold free_slot in H.
  destruct (nth_error t i) as [o |] eqn:E; [| discriminate].
  destruct o as [s0 |]; [| discriminate].
  injection H as H0 H1; subst.
  split.
  - reflexivity.
  - apply nth_error_replace_nth_same.
    apply (proj1 (nth_error_Some t i)). rewrite E. discriminate.
Qed.

(* Honest form: free_slot on a non-occupied slot returns None. *)
Lemma free_slot_nonoccupied_none (t : table) (i : nat)
  (Ho : forall s : cap_slot, nth_error t i <> Some (Some s)) :
  free_slot t i = None.
Proof.
  unfold free_slot.
  destruct (nth_error t i) as [o |]; [| reflexivity].
  destruct o as [s |]; [| reflexivity].
  exfalso. apply (Ho s). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* grant: copy a capability with subset rights, seL4-style.           *)
(* ------------------------------------------------------------------ *)

Definition grant (t : table) (from to : nat) (r : rights) : option table :=
  match nth_error t from with
  | Some (Some src) =>
      if r_subsetb r (slot_rights src)
      then match nth_error t to with
           | Some None => Some (replace_nth to t (Some (mk_cap_slot (slot_ty src) r)))
           | _ => None
           end
      else None
  | _ => None
  end.

Lemma grant_bad_source_none (t : table) (from to : nat) (r : rights)
  (Hsrc : forall s : cap_slot, nth_error t from <> Some (Some s)) :
  grant t from to r = None.
Proof.
  unfold grant.
  destruct (nth_error t from) as [o |]; [| reflexivity].
  destruct o as [s |]; [| reflexivity].
  exfalso. apply (Hsrc s). reflexivity.
Qed.

Lemma grant_amplification_none (t : table) (from to : nat) (r : rights)
  (src : cap_slot) (Hsrc : nth_error t from = Some (Some src))
  (Hamp : r_subsetb r (slot_rights src) = false) :
  grant t from to r = None.
Proof.
  unfold grant. rewrite Hsrc. rewrite Hamp. reflexivity.
Qed.

Lemma grant_occupied_dest_none (t : table) (from to : nat) (r : rights)
  (src : cap_slot) (Hsrc : nth_error t from = Some (Some src))
  (Hsub : r_subsetb r (slot_rights src) = true)
  (s : cap_slot) (Hdest : nth_error t to = Some (Some s)) :
  grant t from to r = None.
Proof.
  unfold grant. rewrite Hsrc. rewrite Hsub. rewrite Hdest. reflexivity.
Qed.

Lemma grant_success_copies (t : table) (from to : nat) (r : rights) (t' : table)
  (H : grant t from to r = Some t') :
  exists src : cap_slot,
    nth_error t from = Some (Some src) /\
    nth_error t' to = Some (Some (mk_cap_slot (slot_ty src) r)) /\
    length t' = length t.
Proof.
  unfold grant in H.
  destruct (nth_error t from) as [o |] eqn:Ef; [| discriminate].
  destruct o as [s |]; [| discriminate].
  destruct (r_subsetb r (slot_rights s)) eqn:Er; [| discriminate].
  destruct (nth_error t to) as [o2 |] eqn:Et; [| discriminate].
  destruct o2 as [s2 |]; [discriminate |].
  injection H as H; subst.
  exists s. split; [ reflexivity | ].
  split.
  - apply nth_error_replace_nth_same.
    apply (proj1 (nth_error_Some t to)). rewrite Et. discriminate.
  - apply length_replace_nth.
Qed.

Lemma grant_preserves_others (t : table) (from to j : nat) (r : rights) (t' : table)
  (H : grant t from to r = Some t') (Hneq : to <> j) :
  nth_error t' j = nth_error t j.
Proof.
  unfold grant in H.
  destruct (nth_error t from) as [o |] eqn:Ef; [| discriminate].
  destruct o as [s |]; [| discriminate].
  destruct (r_subsetb r (slot_rights s)) eqn:Er; [| discriminate].
  destruct (nth_error t to) as [o2 |] eqn:Et; [| discriminate].
  destruct o2 as [s2 |]; [discriminate |].
  injection H as H; subst.
  apply nth_error_replace_nth_other. exact Hneq.
Qed.

(* ================================================================== *)
(* 3. Ports: bounded FIFO queues.                                     *)
(* ================================================================== *)

Definition msg : Set := list nat.

Record port : Set := mk_port {
  port_queue : list msg;
  port_bound : nat;
}.

Definition port_send (p : port) (m : msg) : option port :=
  if length (port_queue p) <? port_bound p
  then Some (mk_port (port_queue p ++ [m]) (port_bound p))
  else None.

Definition port_recv (p : port) : option (msg * port) :=
  match port_queue p with
  | nil => None
  | h :: tl => Some (h, mk_port tl (port_bound p))
  end.

(* send_never_drops: a full port refuses the message. *)
Lemma port_send_full_none (q : list msg) (b : nat) (m : msg)
  (Hfull : length q = b) :
  port_send (mk_port q b) m = None.
Proof.
  unfold port_send.
  change (port_queue (mk_port q b)) with q.
  change (port_bound (mk_port q b)) with b.
  rewrite Hfull. rewrite Nat.ltb_irrefl. reflexivity.
Qed.

(* send_never_drops (positive): a non-full port appends. *)
Lemma port_send_appends (q : list msg) (b : nat) (m : msg)
  (Hfree : length q < b) :
  port_send (mk_port q b) m = Some (mk_port (q ++ [m]) b).
Proof.
  unfold port_send.
  change (port_queue (mk_port q b)) with q.
  change (port_bound (mk_port q b)) with b.
  destruct (length q <? b) eqn:E.
  - reflexivity.
  - apply Nat.ltb_lt in Hfree. rewrite Hfree in E. discriminate.
Qed.

(* recv_empty: an empty queue errors, state unchanged. *)
Lemma port_recv_empty_none (b : nat) : port_recv (mk_port nil b) = None.
Proof. reflexivity. Qed.

(* recv_fifo: two sends from an empty queue, then two recvs, return the
   messages in order.  (port_send is fallible, so the two sends are bound
   through a match.) *)
Lemma port_recv_fifo (b : nat) (H0 : 0 < b) (H1 : 1 < b) (m1 m2 : msg) :
  match port_send (mk_port nil b) m1 with
  | Some p1 =>
      match port_send p1 m2 with
      | Some p2 => port_recv p2
      | None => None
      end
  | None => None
  end = Some (m1, mk_port [m2] b).
Proof.
  unfold port_send, port_recv.
  simpl.
  destruct b as [| [| b''] ].
  - exfalso. lia.
  - exfalso. lia.
  - simpl. reflexivity.
Qed.

(* ================================================================== *)
(* 4. Cap-gated send: the task table gates access (cap_unforgeable).  *)
(* ================================================================== *)

Fixpoint has_port_cap (t : table) (pid : nat) (need : rights) : bool :=
  match t with
  | nil => false
  | Some (mk_cap_slot (CPort p) r) :: tl =>
      if Nat.eqb p pid && r_subsetb need r then true else has_port_cap tl pid need
  | _ :: tl => has_port_cap tl pid need
  end.

(* Soundness: if the gate opens, some slot holds a matching port cap. *)
Lemma has_port_cap_sound (t : table) (pid : nat) (need : rights)
  (H : has_port_cap t pid need = true) :
  exists i s, nth_error t i = Some (Some s) /\
              slot_ty s = CPort pid /\
              r_subsetb need (slot_rights s) = true.
Proof.
  induction t as [| o tl IH]; simpl in H.
  - discriminate.
  - destruct o as [s |].
    + destruct s as [ty r].
      destruct ty as [p | base pages]; simpl in H.
      * destruct (Nat.eqb p pid && r_subsetb need r) eqn:E; simpl in H.
        -- apply andb_true_iff in E as [Ep Er].
           exists 0, (mk_cap_slot (CPort p) r). simpl.
           split; [ reflexivity | ].
           split; [ f_equal; apply Nat.eqb_eq in Ep; exact Ep | exact Er ].
        -- apply IH in H. destruct H as [i [s0 [Hn [Ht Hr]]]].
           exists (S i), s0. simpl. split; [ exact Hn | ].
           split; [ exact Ht | exact Hr ].
      * apply IH in H. destruct H as [i [s0 [Hn [Ht Hr]]]].
        exists (S i), s0. simpl. split; [ exact Hn | ].
        split; [ exact Ht | exact Hr ].
    + apply IH in H. destruct H as [i [s0 [Hn [Ht Hr]]]].
      exists (S i), s0. simpl. split; [ exact Hn | ].
      split; [ exact Ht | exact Hr ].
Qed.

(* cap_unforgeable (negative): an empty table opens no gates. *)
Lemma has_port_cap_nil_false (pid : nat) (need : rights) :
  has_port_cap nil pid need = false.
Proof. reflexivity. Qed.

(* The gate opens after a successful grant of the port cap. *)
Lemma has_port_cap_replace_nth (t : table) (i pid : nat) (sr r : rights)
  (Hin : i < length t) (Hsub : r_subsetb r sr = true) :
  has_port_cap (replace_nth i t (Some (mk_cap_slot (CPort pid) sr))) pid r = true.
Proof.
  revert i Hin. induction t as [| a tl IHt]; intros i Hin; simpl in Hin.
  - lia.
  - destruct i as [| i'].
    + simpl. rewrite Nat.eqb_refl. rewrite Hsub. reflexivity.
    + apply Nat.lt_succ_lt_pred in Hin. simpl in Hin. simpl.
      destruct a as [s |].
      * destruct s as [ty r0].
        destruct ty as [p | base pages]; simpl.
        -- destruct (Nat.eqb p pid && r_subsetb r r0) eqn:E; [ reflexivity | ].
           apply IHt. exact Hin.
        -- apply IHt. exact Hin.
      * simpl. apply IHt. exact Hin.
Qed.

Lemma has_port_cap_after_grant (t : table) (from to pid : nat) (r : rights) (t' : table)
  (H : grant t from to r = Some t')
  (Hty : forall s : cap_slot, nth_error t from = Some (Some s) -> slot_ty s = CPort pid) :
  has_port_cap t' pid r = true.
Proof.
  unfold grant in H.
  destruct (nth_error t from) as [o |] eqn:Ef; [| discriminate].
  destruct o as [s |]; [| discriminate].
  destruct (r_subsetb r (slot_rights s)) eqn:Er; [| discriminate].
  destruct (nth_error t to) as [o2 |] eqn:Et; [| discriminate].
  destruct o2 as [s2 |]; [discriminate |].
  injection H as H; subst.
  rewrite (Hty s eq_refl).
  eapply has_port_cap_replace_nth.
  - apply (proj1 (nth_error_Some t to)). rewrite Et. discriminate.
  - apply r_subsetb_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* gated_send: a task sends iff its table holds the port cap.         *)
(* ------------------------------------------------------------------ *)

Record gated_port : Set := mk_gp {
  gp_table : table;
  gp_port  : port;
}.

Definition gated_send (g : gated_port) (pid : nat) (need : rights) (m : msg) :
  option gated_port :=
  if has_port_cap (gp_table g) pid need
  then match port_send (gp_port g) m with
       | Some p => Some (mk_gp (gp_table g) p)
       | None => None
       end
  else None.

(* The gate is necessary: a successful send implies the cap was held. *)
Lemma gated_send_requires_cap (g : gated_port) (pid : nat) (need : rights) (m : msg)
  (g' : gated_port) (H : gated_send g pid need m = Some g') :
  has_port_cap (gp_table g) pid need = true.
Proof.
  unfold gated_send in H.
  destruct (has_port_cap (gp_table g) pid need) eqn:E; [ reflexivity | discriminate ].
Qed.

(* cap_unforgeable: without the cap the send is refused, state unchanged. *)
Lemma gated_send_no_cap_none (g : gated_port) (pid : nat) (need : rights) (m : msg)
  (H : has_port_cap (gp_table g) pid need = false) :
  gated_send g pid need m = None.
Proof.
  unfold gated_send. rewrite H. reflexivity.
Qed.

(* Combined: an empty table cannot send — the minimal unforgeability
   statement, matching `cap_unforgeable` in the Iris spec. *)
Lemma cap_unforgeable (g : gated_port) (pid : nat) (need : rights) (m : msg)
  (H : gp_table g = nil) :
  gated_send g pid need m = None.
Proof.
  unfold gated_send. rewrite H. reflexivity.
Qed.

(* gated_send moves the message into the queue (ownership transfer). *)
Lemma gated_send_queues_msg (g : gated_port) (pid : nat) (need : rights) (m : msg)
  (Hcap : has_port_cap (gp_table g) pid need = true)
  (g' : gated_port) (H : gated_send g pid need m = Some g') :
  port_queue (gp_port g') = port_queue (gp_port g) ++ [m].
Proof.
  unfold gated_send in H. rewrite Hcap in H.
  destruct (port_send (gp_port g) m) as [p |] eqn:E; [| discriminate].
  injection H as H; subst.
  unfold port_send in E.
  destruct (length (port_queue (gp_port g)) <? port_bound (gp_port g)) eqn:El; [| discriminate].
  injection E as E; subst. simpl. reflexivity.
Qed.

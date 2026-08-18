(* Tessera — SSG-3: interrupt priority selection (the AIA `*topei` / GIC ICC_IAR
   highest-priority pick), modelled as a pure function over the per-hart
   interrupt file.

   intc.sail models ONE shootdown IPI per hart (a single pending bit), so the
   doorbell refinement (intc_proofs.v) never needs to *choose* among interrupts.
   A real controller does: `*topei`/ICC_IAR return the highest-priority
   pending-and-enabled interrupt.  This file is that selection, pinned against
   the primary sources:

     - RISC-V AIA IMSIC.adoc: "The value of a `*topei` CSR indicates the
       interrupt file's current highest-priority pending-and-enabled interrupt
       that also exceeds the priority threshold specified by its `eithreshold`
       register if `eithreshold` is not zero. Interrupts with lower identity
       numbers have higher priorities."  A read returns zero iff nothing is
       pending-and-enabled, or nothing eligible is below `eithreshold`.
     - Arm IHI 0069: ICC_IAR returns the INTID of the highest-priority pending
       interrupt subject to the priority mask/filter (ICC_PMR, ICC_BPR).

   So `topei` = the *least* interrupt identity i such that
       pending[i] ∧ enabled[i] ∧ (threshold = 0 ∨ i < threshold),
   or None when no such i exists (the 1023 / zero "spurious" read).

   What is proved here:
     * soundness  — `topei = Some k` ⇒ k is pending ∧ enabled ∧ below threshold;
     * minimality — k is the *first* (highest-priority) eligible identity;
     * completeness — `topei = None` ⇐ no eligible identity;
     * priority   — a higher-priority pending+enabled interrupt is selected over
                    a lower-priority one.
   plus executable `vm_compute` vectors pinning the picks.

   See doc/system-state-goals.md (SSG-3) and doc/interrupt-controller.md. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.
Open Scope bool_scope.

(* Eligible: identity i is pending, enabled, and above the priority threshold
   (`threshold = 0` means "no threshold": every identity is eligible). *)
Definition eligible (pending enabled : list bool) (threshold i : nat) : bool :=
  match nth_error pending i, nth_error enabled i with
  | Some p, Some e => p && e && (Nat.eqb threshold 0 || Nat.ltb i threshold)
  | _, _ => false
  end.

(* The `*topei` scan: the least eligible identity (lowest identity number =
   highest priority), carrying the absolute identity in `off`. *)
Fixpoint topei_aux (pending enabled : list bool) (threshold off : nat) : option nat :=
  match pending, enabled with
  | [], _ => None
  | _, [] => None
  | p :: ps, e :: es =>
      if p && e && (Nat.eqb threshold 0 || Nat.ltb off threshold)
      then Some off
      else topei_aux ps es threshold (S off)
  end.

Definition topei (pending enabled : list bool) (threshold : nat) : option nat :=
  topei_aux pending enabled threshold 0.

(* `nth_error` recurses on the *index*, so an application at a variable index is
   stuck for `simpl`/`reflexivity`.  This pins the empty-list case so the scans
   below can compute. *)
Lemma nth_error_nil {A : Type} (d : nat) : nth_error ([] : list A) d = None.
Proof. destruct d; reflexivity. Qed.

(* ============================================================
   Soundness: `topei` only ever selects an eligible identity.
   ============================================================ *)

(* The offset-carrying form: a `Some k` at offset `off` is at-or-after `off` and
   eligible at absolute identity k. *)
Lemma topei_aux_some_eligible (p e : list bool) (t off k : nat) :
  topei_aux p e t off = Some k ->
  off <= k /\
  (match nth_error p (k - off), nth_error e (k - off) with
   | Some pb, Some eb => pb && eb && (Nat.eqb t 0 || Nat.ltb k t) = true
   | _, _ => False
   end).
Proof.
  revert e off k. induction p as [| pb ps IH]; intros e off k Hk; cbn [topei_aux] in Hk.
  - discriminate.
  - destruct e as [| eb es]; cbn [topei_aux] in Hk; [discriminate |].
    destruct (pb && eb && (Nat.eqb t 0 || Nat.ltb off t)) eqn:E.
    + injection Hk as ->. split.
      * lia.
      * cbn [nth_error]. replace (k - k) with 0 by lia. cbn [nth_error].
        rewrite E. reflexivity.
    + specialize (IH es (S off) k Hk) as [Hlek HkE]. split.
      * lia.
      * cbn [nth_error].
        replace (k - off) with (S (k - S off)) by lia.
        cbn [nth_error]. exact HkE.
Qed.

Lemma topei_some_eligible (p e : list bool) (t k : nat) :
  topei p e t = Some k -> eligible p e t k = true.
Proof.
  unfold topei, eligible. intro Hk.
  destruct (topei_aux_some_eligible p e t 0 k Hk) as [_ HkE].
  rewrite Nat.sub_0_r in HkE.
  destruct (nth_error p k) as [pb |]; [| exfalso; exact HkE].
  destruct (nth_error e k) as [eb |]; [| exfalso; exact HkE].
  exact HkE.
Qed.

(* ============================================================
   Minimality: `topei` returns the FIRST eligible identity, so a lower identity
   number (higher priority) that is eligible is never skipped over.
   ============================================================ *)

Lemma topei_aux_minimal (p e : list bool) (t off k : nat) :
  topei_aux p e t off = Some k ->
  forall d, d < k - off ->
    match nth_error p d, nth_error e d with
    | Some pb, Some eb => pb && eb && (Nat.eqb t 0 || Nat.ltb (off + d) t) = false
    | _, _ => True
    end.
Proof.
  revert e off k. induction p as [| pb ps IH]; intros e off k Hk; cbn [topei_aux] in Hk.
  - discriminate.
  - destruct e as [| eb es]; cbn [topei_aux] in Hk; [discriminate |].
    destruct (pb && eb && (Nat.eqb t 0 || Nat.ltb off t)) eqn:E.
    + injection Hk as ->.
      intros d Hd. lia.
    + specialize (IH es (S off) k Hk).
      intros d Hd.
      destruct d as [| d'].
      * cbn [nth_error]. rewrite Nat.add_0_r. exact E.
      * cbn [nth_error]. replace (off + S d') with (S off + d') by lia.
        apply (IH d'). lia.
Qed.

Lemma topei_minimal (p e : list bool) (t k : nat) :
  topei p e t = Some k -> forall j, j < k -> eligible p e t j = false.
Proof.
  unfold topei, eligible. intros Hk j Hj.
  assert (Hm := topei_aux_minimal p e t 0 k Hk j).
  rewrite Nat.sub_0_r in Hm.
  specialize (Hm Hj).
  cbn [Nat.add] in Hm.
  destruct (nth_error p j) as [pb |]; [| reflexivity].
  destruct (nth_error e j) as [eb |]; [| reflexivity].
  exact Hm.
Qed.

(* ============================================================
   Completeness: no eligible identity ⇒ None.
   ============================================================ *)

Lemma topei_aux_none (p e : list bool) (t off : nat) :
  topei_aux p e t off = None ->
  forall d, match nth_error p d, nth_error e d with
    | Some pb, Some eb => pb && eb && (Nat.eqb t 0 || Nat.ltb (off + d) t) = false
    | _, _ => True
    end.
Proof.
  revert e off. induction p as [| pb ps IH]; intros e off Hk; cbn [topei_aux] in Hk.
  - intros d. rewrite (nth_error_nil (A := bool) d). reflexivity.
  - destruct e as [| eb es]; cbn [topei_aux] in Hk;
      [intros d; rewrite (nth_error_nil (A := bool) d);
       destruct (nth_error (pb :: ps) d) as [pb' |]; reflexivity |].
    destruct (pb && eb && (Nat.eqb t 0 || Nat.ltb off t)) eqn:E.
    + discriminate.
    + specialize (IH es (S off) Hk).
      intros d.
      destruct d as [| d'].
      * cbn [nth_error]. rewrite Nat.add_0_r. exact E.
      * cbn [nth_error]. replace (off + S d') with (S off + d') by lia.
        apply (IH d').
Qed.

Lemma topei_none_no_eligible (p e : list bool) (t : nat) :
  topei p e t = None -> forall j, eligible p e t j = false.
Proof.
  unfold topei, eligible. intros Hk j.
  assert (Hn := topei_aux_none p e t 0 Hk j).
  cbn [Nat.add] in Hn.
  destruct (nth_error p j) as [pb |]; [| reflexivity].
  destruct (nth_error e j) as [eb |]; [| reflexivity].
  exact Hn.
Qed.

(* ============================================================
   Priority: a higher-priority (lower-identity) eligible interrupt is selected
   over a lower-priority one.
   ============================================================ *)

Lemma topei_priority (p e : list bool) (t a b : nat) :
  eligible p e t a = true -> eligible p e t b = true -> a < b ->
  topei p e t <> Some b.
Proof.
  intros Ha Hb Hab Hb'.
  pose proof (topei_minimal p e t b Hb') as Hmin.
  specialize (Hmin a Hab).
  congruence.
Qed.

(* ============================================================
   Executable vectors (vm_compute).
   ============================================================ *)

(* Interrupts 2 and 5 pending, both enabled: the lowest identity (highest
   priority) is selected. *)
Lemma test_vector_topei_highest_priority :
  topei [false; false; true; false; false; true]
        [true;  true;  true; true;  true;  true] 0 = Some 2.
Proof. vm_compute. reflexivity. Qed.

(* A higher-priority (id 1) interrupt that is *disabled* is skipped, so the
   lower-priority enabled id 2 is selected. *)
Lemma test_vector_topei_skips_disabled :
  topei [false; true; true] [true; false; true] 0 = Some 2.
Proof. vm_compute. reflexivity. Qed.

(* The priority threshold (eithreshold) masks identities at-or-above it. *)
Lemma test_vector_topei_threshold :
  topei [false; false; true; true] [true; true; true; true] 3 = Some 2.
Proof. vm_compute. reflexivity. Qed.

(* ...and can mask everything, returning None (the zero / 1023 read). *)
Lemma test_vector_topei_threshold_masks_all :
  topei [false; true] [true; true] 1 = None.
Proof. vm_compute. reflexivity. Qed.

(* Nothing pending ⇒ None. *)
Lemma test_vector_topei_none :
  topei [false; false; false] [true; true; true] 0 = None.
Proof. vm_compute. reflexivity. Qed.

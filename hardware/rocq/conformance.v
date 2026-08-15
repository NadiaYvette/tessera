(* Tessera — G1 conformance: the hand-written Sv39 walk vs the upstream walker.

   `machine.sail`'s `translate` is a hand-written, ~180-line Sv39 walk.  G1
   (rigor-trust-line.md) is the gap: it is not validated against the upstream
   `sail-riscv` model.  This file closes the *conformance-test* half of G1 by
   transcribing the upstream walker and proving `translate` agrees with it.

   The oracle below is a faithful transcription of the upstream Sv39 page-table
   walk, restricted to the *leaf-only level-0 fragment* the hand-written model
   targets:

     - `oracle_pte_non_leaf p`  ≜  ¬R ∧ ¬W ∧ ¬X
         (sail-riscv model/sys/vmem_pte.sail, `pte_is_non_leaf`, ll. 69-71)
     - `oracle_pte_invalid p`   ≜  ¬V ∨ (W ∧ ¬R)
         (sail-riscv model/sys/vmem_pte.sail, `pte_is_invalid`, ll. 89-108:
          V=0, or the reserved write-only encodings R=0,W=1 — the A/D/U/G/N/PBMT
          and shadow-stack clauses are vacuously 0 on this fragment)
     - the walk structure (invalid ⇒ fault; non-leaf ⇒ recurse; leaf at level>0 ⇒
          superpage — here FAULT, the fragment does not model superpages; leaf at
          level 0 ⇒ succeed) follows
         (sail-riscv model/sys/vmem.sail, `pt_walk`, ll. 101-208).

   The oracle reuses the *same* `Pte`/`PageTable`/`pte_address`/`phys_addr`/
   `read_pte`/`perm_of_pte` as the model, so the one remaining trust step is the
   struct↔word bitfield encoding (Pte.V/R/W/X/U = word bits 0/1/2/3/4, ppn =
   bits 53..10) — a small, reviewable correspondence, documented rather than
   re-proved here.

   The headline theorem `translate_conforms` proves exact agreement (same PA,
   same permission, same fault) on the **no-write-only fragment**: every PTE in
   the table has ¬(W ∧ ¬R).  This also *surfaces* the one known delta the
   hand-written model still has against the spec — a write-only (R=0,W=1) PTE is
   reserved in Sv39 (the walk must fault) but the current `translate` treats it
   as a readable leaf.  That delta is excluded by `no_writeonly` and queued for a
   follow-up fix; see rigor-trust-line.md G1. *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.  (* eq_vec_true_iff *)
Require Import machine_types.
Require Import machine.
Import ListNotations.

(* ============================================================
   The oracle (upstream Sv39 walk, leaf-only fragment).
   ============================================================ *)

Definition oracle_pte_invalid (p : Pte) : bool :=
  negb p.(Pte_valid) || (p.(Pte_write) && negb p.(Pte_read)).

Definition oracle_pte_non_leaf (p : Pte) : bool :=
  negb p.(Pte_read) && negb p.(Pte_write) && negb p.(Pte_exec).

Definition oracle_walk (satp : mword 44) (mem : PageTable) (va : mword 64)
  : option (mword 56 * Perm) :=
  match read_pte mem (pte_address satp (vpn2 va)) with
  | None => None
  | Some p2 =>
      if oracle_pte_invalid p2 then None
      else if oracle_pte_non_leaf p2 then
        match read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va)) with
        | None => None
        | Some p1 =>
            if oracle_pte_invalid p1 then None
            else if oracle_pte_non_leaf p1 then
              match read_pte mem (pte_address p1.(Pte_ppn) (vpn0 va)) with
              | None => None
              | Some p0 =>
                  if oracle_pte_invalid p0 then None
                  else if oracle_pte_non_leaf p0 then None   (* level-0 pointer *)
                  else Some (phys_addr p0.(Pte_ppn) (page_offset va), perm_of_pte p0)
              end
            else None   (* level-1 superpage: fragment faults *)
        end
      else None   (* level-2 superpage: fragment faults *)
  end.

(* ============================================================
   The fragment: no write-only (R=0, W=1) PTE anywhere in the table.
   ============================================================ *)

Definition no_writeonly (mem : PageTable) : Prop :=
  Forall (fun e => e.(MemEntry_pte).(Pte_write) = false \/ e.(MemEntry_pte).(Pte_read) = true) mem.

(* `read_pte` returns a PTE that really is in the table. *)
Lemma read_pte_In (mem : PageTable) (a : mword 56) (p : Pte) :
  read_pte mem a = Some p -> In {| MemEntry_addr := a; MemEntry_pte := p |} mem.
Proof.
  induction mem as [| e rest IH]; cbn.
  - intros H. discriminate.
  - destruct (eq_vec e.(MemEntry_addr) a) eqn:E.
    + intros H. injection H as Hp. apply eq_vec_true_iff in E.
      left. destruct e as [ea ep]. cbn in *. subst. reflexivity.
    + intros H. right. apply IH. exact H.
Qed.

(* A PTE read from a no-write-only table is itself not write-only. *)
Lemma read_pte_nw (mem : PageTable) (a : mword 56) (p : Pte) :
  no_writeonly mem -> read_pte mem a = Some p ->
  p.(Pte_write) = false \/ p.(Pte_read) = true.
Proof.
  intros Hnw Hr.
  apply read_pte_In in Hr.
  unfold no_writeonly in Hnw.
  rewrite Forall_forall in Hnw.
  specialize (Hnw {| MemEntry_addr := a; MemEntry_pte := p |} Hr).
  cbn in Hnw. exact Hnw.
Qed.

(* ============================================================
   The two walks agree.
   ============================================================ *)

(* The oracle's non-leaf predicate is exactly the negation of `is_leaf`. *)
Lemma oracle_non_leaf_is_negb_is_leaf (p : Pte) :
  oracle_pte_non_leaf p = negb (is_leaf p).
Proof.
  unfold oracle_pte_non_leaf, is_leaf.
  destruct p as [v r w x u ppn]; cbn.
  destruct r, w, x; reflexivity.
Qed.

(* The oracle's invalid predicate is just "not valid" on a non-write-only PTE. *)
Lemma oracle_invalid_is_negb_valid (p : Pte) :
  p.(Pte_write) = false \/ p.(Pte_read) = true ->
  oracle_pte_invalid p = negb p.(Pte_valid).
Proof.
  intros H. unfold oracle_pte_invalid.
  destruct p as [v r w x u ppn]; cbn in *.
  destruct H as [Hw | Hr]; subst.
  - destruct v, r; reflexivity.
  - destruct v, w; reflexivity.
Qed.

(* The headline: on the no-write-only fragment, the hand-written walk and the
   upstream walk agree exactly — same physical address, same permission, same
   fault. *)
Theorem translate_conforms (core : Core) (mem : PageTable) (va : mword 64) :
  no_writeonly mem ->
  translate core mem va = oracle_walk core.(Core_satp_ppn) mem va.
Proof.
  intros Hnw.
  unfold translate, oracle_walk.
  destruct (read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va))) as [p2|] eqn:E2; [| reflexivity].
  rewrite (oracle_invalid_is_negb_valid p2 (read_pte_nw mem _ p2 Hnw E2)).
  rewrite (oracle_non_leaf_is_negb_is_leaf p2).
  destruct (read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va))) as [p1|] eqn:E1.
  - rewrite (oracle_invalid_is_negb_valid p1 (read_pte_nw mem _ p1 Hnw E1)).
    rewrite (oracle_non_leaf_is_negb_is_leaf p1).
    destruct (read_pte mem (pte_address p1.(Pte_ppn) (vpn0 va))) as [p0|] eqn:E0.
    + rewrite (oracle_invalid_is_negb_valid p0 (read_pte_nw mem _ p0 Hnw E0)).
      rewrite (oracle_non_leaf_is_negb_is_leaf p0).
      destruct p2.(Pte_valid), (is_leaf p2), p1.(Pte_valid), (is_leaf p1), p0.(Pte_valid), (is_leaf p0);
        reflexivity.
    + destruct p2.(Pte_valid), (is_leaf p2), p1.(Pte_valid), (is_leaf p1); reflexivity.
  - destruct p2.(Pte_valid), (is_leaf p2); reflexivity.
Qed.

(* Tessera — Stage 2, S2.2c: the N-core weak-memory broadcast shootdown over the
   concrete machine, with the machine reification.

   S2.2a proved leader -> remote (the PTE invalidation is observed); S2.2b proved
   remote -> leader (the TLB clear is observed via a release/acquire ack).  This
   file composes the two into the full N-core broadcast under genuine weak memory
   (gpfsl / iRC11 / ORC11):

       leader  =  pte <- #(encode_pte invalid_pte) ;; go <-ʳᵉˡ #1   (break-before-make,
                                                                     release = DSB)
                  ;; fork N remotes ;; wait-all-acks
       remote i =  repeat !ᵃᶜ go ;;                                   (acquire = DSB+ISB)
                   tlb[i] <- #(encode_tlb None) ;;
                   ack[i] <-ʳᵉˡ #1

   The ack barrier is N *single-writer* release/acquire flags (one per remote),
   each exactly the S2.2b pattern (the released branch carries the cleared TLB
   cell via a one-shot UTok ∨ data disjunction).  The leader holds the machine
   ghost OUTSIDE the invariant and advances it in lockstep with ack acquisition:
   after acks 0..i-1 the machine is [bc_machine n i] (cores 0..i-1 cleared, cores
   i..n-1 stale, leaf PTE invalid).  At i = n the machine is exactly
   [broadcast_post_machine], and [broadcast_reifies_machine] (machine_reify.v)
   yields [Forall (translate = None /\ tlb_lookup = None)] on every core.

   gpfsl's value model is LitPoison | LitLoc | LitInt (no product/sum), so the PTE
   and TLB are bit-packed into a Z (encode_pte / encode_tlb from shootdown_weak.v). *)

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import lifting proofmode atomics view_invariants
                                 repeat_loop new_delete.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import own ghost_var.
From iris.proofmode Require Import proofmode monpred.
From gpfsl.base_logic Require Import vprop.
From SailStdpp Require Import MachineWord.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import machine_encoding.   (* invalid_pte/valid_pte, leaf_entry *)
Require Import machine_reify.      (* reify_machine/tls_of/broadcast_*_machine/reifies *)
Require Import shootdown_weak.     (* encode_pte/encode_tlb, UTok, uniqTokG *)
Require Import iris.prelude.options.
Import ListNotations.

(* ============================================================
   Ghost state: only the machine ghost.  The per-core one-shot tokens (UTok)
   and the per-cell sw⊒ writers come from shootdown_weak.v / gpfsl.
   ============================================================ *)

Class bcG Σ := BcG { bc_machineG : ghost_varG Σ Machine; }.
Local Existing Instances bc_machineG.
Definition bcΣ : gFunctors := #[ghost_varΣ Machine].
Global Instance subG_bcΣ {Σ} : subG bcΣ Σ → bcG Σ.
Proof. solve_inG. Qed.

(* The machine ghost, embedded into gpfsl's vProp. *)
Definition machine_ctx `{!bcG Σ} (γm : gname) (m : Machine) : vProp Σ :=
  ⎡ ghost_var γm (DfracOwn 1) m ⎤.

#[global] Instance machine_ctx_objective `{!bcG Σ} γm m : Objective (machine_ctx γm m).
Proof. rewrite /machine_ctx. apply _. Qed.

(* ============================================================
   Pure helpers: the core set and the machine-at-step-i reification.
   ============================================================ *)

Definition all_cores (n : nat) : gset nat := list_to_set (seq 0 n).

Lemma elem_of_all_cores (n i : nat) : i ∈ all_cores n ↔ i < n.
Proof.
  rewrite /all_cores elem_of_list_to_set elem_of_seq. lia.
Qed.

Lemma all_cores_0 : all_cores 0 = ∅.
Proof. rewrite /all_cores. reflexivity. Qed.

Lemma all_cores_diff_empty (n i : nat) : n ≤ i → all_cores n ∖ all_cores i = ∅.
Proof.
  intros Hni. apply subseteq_empty_difference_L. intros x.
  rewrite !elem_of_all_cores. lia.
Qed.

Lemma size_all_cores (n : nat) : size (all_cores n) = n.
Proof.
  rewrite /all_cores size_list_to_set.
  - rewrite length_seq. lia.
  - apply NoDup_seq.
Qed.

Lemma all_cores_step (n i : nat) :
  i < n →
  all_cores n ∖ all_cores i = {[i]} ∪ (all_cores n ∖ all_cores (i + 1)).
Proof.
  intros Hin. apply set_eq. intro x.
  setoid_rewrite elem_of_difference. setoid_rewrite elem_of_union.
  setoid_rewrite elem_of_singleton. setoid_rewrite elem_of_difference.
  setoid_rewrite elem_of_all_cores. intuition lia.
Qed.

(* The machine the leader models at wait-step i: cores 0..i-1 have cleared their
   TLB, cores i..n-1 still cache [leaf_entry va], and the leaf PTE is already
   invalid (the break-before-make write happened before the fork). *)
Definition bc_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n i : nat) : Machine :=
  reify_machine root va mem invalid_pte
    (fun j => if decide (i ≤ j < n) then Some (leaf_entry va) else None) n.

(* ============================================================
   The program.
   ============================================================ *)

Definition bc_remote : expr :=
  λ: ["go"; "ack"; "tlb"; "i"],
    (repeat: !ᵃᶜ("go")) ;;                        (* acquire go: the PTE is published *)
    ("tlb" +ₗ "i") <- #(encode_tlb None) ;;       (* clear own TLB *)
    ("ack" +ₗ "i") <-ʳᵉˡ #1.                      (* release ack: the clear is visible *)

Definition bc_init_acks : expr :=
  rec: "f" ["ack"; "i"; "n"] :=
    if: "i" < "n"
    then ("ack" +ₗ "i" <- #0 ;; "f" ["ack"; ("i" + #1); "n"])
    else #☠.

Definition bc_fork_remotes : expr :=
  rec: "f" ["go"; "ack"; "tlb"; "i"; "n"] :=
    if: "i" < "n"
    then (Fork (bc_remote ["go"; "ack"; "tlb"; "i"]) ;;
          "f" ["go"; "ack"; "tlb"; ("i" + #1); "n"])
    else #☠.

Definition bc_wait_all : expr :=
  rec: "w" ["ack"; "i"; "n"] :=
    if: "i" < "n"
    then ((repeat: !ᵃᶜ("ack" +ₗ "i")) ;; "w" ["ack"; ("i" + #1); "n"])
    else #☠.

Definition bc_broadcast : expr :=
  λ: ["n"],
    let: "pte" := new [ #1] in
    let: "go"  := new [ #1] in
    let: "ack" := new [ "n"] in
    let: "tlb" := new [ "n"] in
    "go" +ₗ #0 <- #0 ;;
    "pte" +ₗ #0 <- #(encode_pte invalid_pte) ;;  (* break-before-make *)
    "go" +ₗ #0 <-ʳᵉˡ #1 ;;                       (* release go *)
    bc_init_acks ["ack"; #0; "n"] ;;
    bc_fork_remotes ["go"; "ack"; "tlb"; #0; "n"] ;;
    bc_wait_all ["ack"; #0; "n"].

(* ============================================================
   The ack cell (S2.2b's one-shot buffer, per remote) and the go flag.
   ============================================================ *)

Implicit Types (x : loc) (γ : gname) (ζ : absHist) (t : time) (V : view).

Section bc_inv.
Context `{!noprolG Σ, !atomicG Σ, !uniqTokG Σ, !bcG Σ}.
Context (γm : gname) (root : mword 44) (va : mword 64) (mem : list MemEntry).
#[local] Abbreviation vProp := (vProp Σ).

(* ack[j] sw↦, one-shot: released (history has a #1 write after the #0 init)
   exactly when the remote has cleared its TLB; the released branch carries
   either the leader's one-shot token (slot empty) or the cleared TLB cell
   (slot full).  This is literally S2.2b's [sd_ack_inv'], per remote. *)
Definition ack_cell_def (x y : loc) (γ γx : gname) : vProp :=
  (∃ ζ (b : bool) t0 V0 Vx,
    @{Vx} (x sw↦{γx} ζ) ∗
    let ζ0 : absHist := {[t0 := (#0, V0)]} in
    match b with
    | false => ⌜ζ = ζ0⌝
    | true  => ∃ t1 V1, ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>ζ0⌝ ∗
                 (UTok γ ∨ @{V1} (y ↦ #(encode_tlb None)))
    end
  )%I.
Definition ack_cell_aux : seal (@ack_cell_def). Proof. by eexists. Qed.
Definition ack_cell := unseal ack_cell_aux.
Definition ack_cell_eq : @ack_cell = _ := seal_eq _.

(* go sw↦, fixed released: history {t0:#0} extended with {t1:#1}, t0 < t1. *)
Definition go_released_def (x : loc) (γx : gname) : vProp :=
  (∃ ζ t0 t1 V0 V1 Vx, @{Vx} (x sw↦{γx} ζ) ∗
    ⌜(t0 < t1)%positive ∧ ζ = <[t1 := (#1, V1)]>{[t0 := (#0, V0)]}⌝)%I.
Definition go_released_aux : seal (@go_released_def). Proof. by eexists. Qed.
Definition go_released := unseal go_released_aux.
Definition go_released_eq : @go_released = _ := seal_eq _.

(* The broadcast invariant: the go flag (fixed released) and, per core, the
   ack cell.  The machine ghost is held by the leader OUTSIDE the invariant. *)
Definition bc_inv_def (γgo : gname) (γtok γack : nat → gname)
                      (go ack tlb : loc) (n : nat) : vProp :=
  (go_released go γgo ∗
   [∗ set] j ∈ all_cores n, ack_cell ((ack >> j)%stdpp) ((tlb >> j)%stdpp)
                                      (γtok j) (γack j))%I.
Definition bc_inv_aux : seal (@bc_inv_def). Proof. by eexists. Qed.
Definition bc_inv := unseal bc_inv_aux.
Definition bc_inv_eq : @bc_inv = _ := seal_eq _.

#[global] Instance ack_cell_objective x y γ γx : Objective (ack_cell x y γ γx).
Proof.
  rewrite ack_cell_eq.
  apply exists_objective=>?. apply exists_objective=>[[|]]; by apply _.
Qed.

#[global] Instance go_released_objective x γx : Objective (go_released x γx).
Proof. rewrite go_released_eq. apply _. Qed.

#[global] Instance bc_inv_objective γgo γtok γack go ack tlb n :
  Objective (bc_inv γgo γtok γack go ack tlb n).
Proof.
  rewrite bc_inv_eq.
  apply sep_objective; [apply go_released_objective|]. apply _.
Qed.

Definition bc_N (n : loc) := nroot .@ "bcN" .@ n.
Definition bc_inv_ctx γgo γtok γack go ack tlb n :=
  inv (bc_N go) (bc_inv γgo γtok γack go ack tlb n).

(* ============================================================
   Pure reification step.
   ============================================================ *)

(* Core i still caches [leaf_entry va] exactly while i ≤ i < n; after the leader
   deletes it the machine steps from [bc_machine n i] to [bc_machine n (i+1)]. *)
Lemma bc_machine_step_Some (n i : nat) (Hin : i < n) :
  (fun j => if decide (i ≤ j < n) then Some (leaf_entry va) else None) i
  = Some (leaf_entry va).
Proof.
  cbn. case_decide as H; [done|exfalso]. apply H. split; [lia|exact Hin].
Qed.

Lemma bc_machine_step_None (n i : nat) :
  (fun j => if decide (i + 1 ≤ j < n) then Some (leaf_entry va) else None) i
  = None.
Proof.
  cbn. case_decide as H; [exfalso; lia|done].
Qed.

End bc_inv.

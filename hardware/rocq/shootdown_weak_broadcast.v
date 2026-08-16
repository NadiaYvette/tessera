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
From gpfsl.base_logic Require Import vprop na meta_data.
From SailStdpp Require Import MachineWord.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import machine_encoding.   (* invalid_pte/valid_pte, leaf_entry *)
Require Import machine_reify.      (* reify_machine/tls_of/broadcast_*_machine/reifies *)
Require Import coherence_leaf.     (* invalidate_leaf_mem *)
Require Import shootdown.          (* core_with_root, invalidate_shootdown_empty_cores *)
Require Import ipi.                (* deliver_ipi/receive_ipi + sfence_at/ipi_broadcast (S2.3) *)
Require Import shootdown_weak.     (* encode_pte/encode_tlb, UTok, uniqTokG *)
Require Import tlb_tags.           (* flush_tlb_entry/…_vivt, flush_tlb_entry_leaf (per-cell coupling) *)
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

(* The leader owns the machine ghost exclusively, so it may step it to any value;
   faithfulness (the ghost always matches the constrained physical state) is by
   construction of the proof, exactly as in S2.1's Honesty note. *)
Lemma machine_ctx_update `{!bcG Σ} (γm : gname) (m m' : Machine) :
  machine_ctx γm m ⊢ |==> machine_ctx γm m' : vProp Σ.
Proof.
  rewrite /machine_ctx. iIntros "Hm".
  iMod (ghost_var_update m' γm m with "Hm") as "Hm'".
  iIntros "!>". by iFrame.
Qed.

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

(* The i = 0 base cases of the loop specs mention [all_cores n ∖ all_cores 0];
   [new] produces the whole set [all_cores n], so bridge them here. *)
Lemma all_cores_n_diff_0 (n : nat) : all_cores n = all_cores n ∖ all_cores 0.
Proof. rewrite all_cores_0 difference_empty_L. done. Qed.

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

Lemma all_cores_succ (i : nat) : all_cores (i + 1) = all_cores i ∪ {[i]}.
Proof.
  apply set_eq. intro x.
  rewrite elem_of_union elem_of_singleton !elem_of_all_cores Nat.add_1_r.
  lia.
Qed.

(* The IPI mailbox: core j's shootdown IPI is delivered exactly when j < i. *)
Definition ipi_prefix (n i : nat) : list bool :=
  List.map (fun (j : nat) => bool_decide (j < i)) (seq 0 n).

(* The machine the leader models at wait-step i: cores 0..i-1 have cleared their
   TLB and had their IPI delivered, cores i..n-1 still cache [leaf_entry va] with
   their IPI undelivered, and the leaf PTE is already invalid (the break-before-
   make write happened before the fork).  The [Machine_ipi] mailbox carries the
   delivered bits, so the ghost step below is literally [deliver_ipi]/[receive_ipi]. *)
Definition bc_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n i : nat) : Machine :=
  {| Machine_mem := invalidate_leaf_mem (core_with_root root) mem va invalid_pte;
     Machine_cores := List.map (fun (j : nat) => reify_core root
                             (if decide (i ≤ j < n) then Some (leaf_entry va) else None)) (seq 0 n);
     Machine_ram := [];
     Machine_ipi := ipi_prefix n i |}.

(* The post-machine: every core's IPI delivered and TLB cleared. *)
Definition bc_post_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) : Machine :=
  bc_machine root va mem n n.

(* The pre-machine S2.3b's [ipi_broadcast] starts from: the leaf PTE for [va] is
   still mapped (the break-before-make write has not happened), every core caches
   the stale [leaf_entry va], and no IPI is delivered.  [ipi_broadcast] on this
   machine first writes the invalid PTE, then delivers+receives on every core —
   exactly the S2.4 leader's [bc_machine] ghost sequence (whose step-0 state is
   this machine after the break-before-make write). *)
Definition bc_pre_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) : Machine :=
  {| Machine_mem := mem;
     Machine_cores := List.map (fun _ => reify_core root (Some (leaf_entry va))) (seq 0 n);
     Machine_ram := [];
     Machine_ipi := ipi_prefix n 0 |}.

(* ============================================================
   The program.
   ============================================================ *)

Definition bc_remote : val :=
  λ: ["go"; "ack"; "tlb"; "i"],
    (repeat: !ᵃᶜ("go")) ;;                        (* acquire go: the PTE is published *)
    ("tlb" +ₗ "i") <- #(encode_tlb None) ;;       (* clear own TLB *)
    ("ack" +ₗ "i") <-ʳᵉˡ #1.                      (* release ack: the clear is visible *)

Definition bc_init_acks : val :=
  rec: "f" ["ack"; "i"; "n"] :=
    if: "i" < "n"
    then ("ack" +ₗ "i" <- #0 ;; "f" ["ack"; ("i" + #1); "n"])
    else #☠.

Definition bc_fork_remotes : val :=
  rec: "f" ["go"; "ack"; "tlb"; "i"; "n"] :=
    if: "i" < "n"
    then (Fork (bc_remote ["go"; "ack"; "tlb"; "i"]) ;;
          "f" ["go"; "ack"; "tlb"; ("i" + #1); "n"])
    else #☠.

Definition bc_wait_all : val :=
  rec: "w" ["ack"; "i"; "n"] :=
    if: "i" < "n"
    then ((repeat: !ᵃᶜ("ack" +ₗ "i")) ;; "w" ["ack"; ("i" + #1); "n"])
    else #☠.

Definition bc_broadcast (n : nat) : expr :=
  let: "pte" := new [ #1] in
  let: "go"  := new [ #1] in
  let: "ack" := new [ #(Z.of_nat n)] in
  let: "tlb" := new [ #(Z.of_nat n)] in
  "go" +ₗ #0 <- #0 ;;
  "pte" +ₗ #0 <- #(encode_pte invalid_pte) ;;  (* break-before-make *)
  "go" +ₗ #0 <-ʳᵉˡ #1 ;;                       (* release go *)
  bc_init_acks ["ack"; #0; #(Z.of_nat n)] ;;
  bc_fork_remotes ["go"; "ack"; "tlb"; #0; #(Z.of_nat n)] ;;
  bc_wait_all ["ack"; #0; #(Z.of_nat n)].

(* Application helpers: the [ # ] literal notation does not survive the list
   application (it binds to the head via the App coercion), so we write the
   literal arguments explicitly. *)
Definition bc_remote_at (go ack tlb : loc) (i : nat) : expr :=
  App bc_remote [Lit (LitLoc go); Lit (LitLoc ack); Lit (LitLoc tlb); Lit (LitInt (Z.of_nat i))].
Definition bc_init_acks_at (ack : loc) (i n : nat) : expr :=
  App bc_init_acks [Lit (LitLoc ack); Lit (LitInt (Z.of_nat i)); Lit (LitInt (Z.of_nat n))].
Definition bc_fork_remotes_at (go ack tlb : loc) (i n : nat) : expr :=
  App bc_fork_remotes [Lit (LitLoc go); Lit (LitLoc ack); Lit (LitLoc tlb);
                       Lit (LitInt (Z.of_nat i)); Lit (LitInt (Z.of_nat n))].
Definition bc_wait_all_at (ack : loc) (i n : nat) : expr :=
  App bc_wait_all [Lit (LitLoc ack); Lit (LitInt (Z.of_nat i)); Lit (LitInt (Z.of_nat n))].
Definition bc_broadcast_at (n : nat) : expr := bc_broadcast n.

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
                 (UTok γ ∨ @{V1} (y ↦ #(encode_tlb (flush_tlb_entry (Some (leaf_entry va)) va))))
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

(* The leader's persistent reader context: the SyncSeen view of each ack cell
   (a #0 singleton at [t j]) plus the SeenView of its allocation view [V j].
   Derived once from AtomicPtsTo_from_na in the broadcast setup and shared with
   every wait/read. *)
Definition bc_sync_ctx (γack : nat → gname) (ack : loc)
                       (t : nat → positive) (V : nat → view) (n : nat) : vProp :=
  [∗ set] j ∈ all_cores n,
    ((ack >> j)%stdpp sy⊒{γack j} {[t j := (#0, V j)]} ∗ ⊒(V j))%I.

(* ============================================================
   Pure reification step: the ghost's deliver_ipi + receive_ipi.
   ============================================================ *)

(* [eq_vec x x] is true: the generated mword equality is reflexive. *)
Lemma eq_vec_refl {n} (x : mword n) : eq_vec x x = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.

(* SFENCE.VMA-by-VA empties a core caching exactly [leaf_entry va]. *)
Lemma sfence_vma_va_reify (r : mword 44) (a : mword 64) :
  sfence_vma_va (reify_core r (Some (leaf_entry a))) a = reify_core r None.
Proof.
  rewrite /reify_core /sfence_vma_va /leaf_entry.
  cbn [Core_satp_ppn Core_tlb filter_tlb TlbEntry_vpn].
  rewrite (eq_vec_refl (vpn_of a)). reflexivity.
Qed.

(* [seq (S s) n] is [S] shifted over [seq s n]. *)
Lemma seq_S_shift (s n : nat) : seq (S s) n = List.map S (seq s n).
Proof.
  revert s. induction n as [| n' IH]; intros s; cbn [seq List.map].
  - reflexivity.
  - f_equal. apply IH.
Qed.

(* Pointwise helpers: shifting the index past a [map] on [seq 0 n]. *)
Lemma if_decide_S_eq (j i : nat) (A : Type) (x y : A) :
  (if decide (S j = S i) then x else y) = (if decide (j = i) then x else y).
Proof.
  case_decide as H.
  - case_decide as H'.
    + reflexivity.
    + exfalso. apply H'. lia.
  - case_decide as H'.
    + exfalso. apply H. lia.
    + reflexivity.
Qed.

Lemma if_decide_S_ne_0 (j : nat) (A : Type) (x y : A) :
  (if decide (S j = (0 : nat)) then x else y) = y.
Proof. case_decide as H; [lia | reflexivity]. Qed.

(* [sfence_at] at index i of a [map f (seq 0 n)] updates only the i-th cell. *)
Lemma sfence_at_map_seq (f : nat → Core) (n i : nat) (a : mword 64) :
  sfence_at (List.map f (seq 0 n)) i a =
  List.map (fun j => if decide (j = i) then sfence_vma_va (f j) a else f j) (seq 0 n).
Proof.
  revert f i. induction n as [| n' IH]; intros f [| i'].
  - cbn [seq List.map sfence_at]. reflexivity.
  - cbn [seq List.map sfence_at]. reflexivity.
  - cbn [seq List.map sfence_at]. f_equal.
    rewrite (seq_S_shift 0 n'). rewrite !List.map_map.
    apply List.map_ext. intros j.
    rewrite (if_decide_S_ne_0 j Core (sfence_vma_va (f (S j)) a) (f (S j))).
    reflexivity.
  - cbn [seq List.map sfence_at]. f_equal.
    rewrite (seq_S_shift 0 n'). rewrite !List.map_map.
    rewrite (IH (fun x : nat => f (S x)) i').
    apply List.map_ext. intros j.
    rewrite (if_decide_S_eq j i' Core (sfence_vma_va (f (S j)) a) (f (S j))).
    reflexivity.
Qed.

(* [list_update_bool] at index i of a [map f (seq 0 n)] updates only the i-th cell. *)
Lemma list_update_bool_map_seq (f : nat → bool) (n i : nat) (v : bool) :
  list_update_bool (List.map f (seq 0 n)) (Z.of_nat i) v =
  List.map (fun j => if decide (j = i) then v else f j) (seq 0 n).
Proof.
  revert f i. induction n as [| n' IH]; intros f [| i'].
  - cbn [seq List.map list_update_bool]. reflexivity.
  - cbn [seq List.map list_update_bool]. reflexivity.
  - cbn [seq List.map list_update_bool].
    change (Z.of_nat 0) with 0%Z. cbn [Z.eqb]. f_equal.
    rewrite (seq_S_shift 0 n'). rewrite !List.map_map.
    apply List.map_ext. intros j.
    rewrite (if_decide_S_ne_0 j bool v (f (S j))). reflexivity.
  - cbn [seq List.map list_update_bool].
    destruct (Z.eqb (Z.of_nat (S i')) 0) eqn:E.
    + apply Z.eqb_eq in E. lia.
    + f_equal.
      replace (Z.sub (Z.of_nat (S i')) 1) with (Z.of_nat i') by lia.
      rewrite (seq_S_shift 0 n'). rewrite !List.map_map.
      rewrite (IH (fun x : nat => f (S x)) i').
      apply List.map_ext. intros j.
      rewrite (if_decide_S_eq j i' bool v (f (S j))). reflexivity.
Qed.

(* For j ≠ i, [i ≤ j < n] and [i+1 ≤ j < n] decide the same, so the two
   [if decide] branches agree. *)
Lemma decide_le_succ (i j n : nat) (Hne : j ≠ i) (A : Type) (x y : A) :
  (if decide (i ≤ j < n) then x else y) = (if decide ((i + 1)%nat ≤ j < n) then x else y).
Proof.
  case_decide as H1.
  - case_decide as H2.
    + reflexivity.
    + exfalso. apply Hne. lia.
  - case_decide as H2.
    + exfalso. apply H1. lia.
    + reflexivity.
Qed.

(* The ipi mailbox advances by setting index i: ipi_prefix n (i+1) = set i. *)
Lemma ipi_prefix_step (n i : nat) (Hin : i < n) :
  ipi_prefix n (i + 1) = list_update_bool (ipi_prefix n i) (Z.of_nat i) true.
Proof.
  rewrite /ipi_prefix. rewrite list_update_bool_map_seq.
  apply List.map_ext. intros j.
  destruct (decide (j = i)) as [Hj | Hj].
  - subst.
    rewrite bool_decide_true; [| lia].
    reflexivity.
  - destruct (decide (j < i)) as [H1 | H1];
    destruct (decide (j < (i + 1)%nat)) as [H2 | H2].
    + rewrite bool_decide_true; [| exact H2].
      rewrite bool_decide_true; [| exact H1]. reflexivity.
    + exfalso. lia.
    + exfalso. lia.
    + rewrite bool_decide_false; [| exact H2].
      rewrite bool_decide_false; [| exact H1]. reflexivity.
Qed.

(* Flushing core i of the i-th ghost step gives the (i+1)-th cores list. *)
Lemma bc_cores_ipi_step (n i : nat) (Hin : i < n) :
  List.map (fun (j : nat) => reify_core root (if decide ((i + 1)%nat ≤ j < n) then Some (leaf_entry va) else None)) (seq 0 n)
  = sfence_at (List.map (fun (j : nat) => reify_core root (if decide (i ≤ j < n) then Some (leaf_entry va) else None)) (seq 0 n)) i va.
Proof.
  rewrite sfence_at_map_seq.
  apply List.map_ext. intros j.
  destruct (decide (j = i)) as [Hj | Hj].
  - subst.
    destruct (decide ((i + 1)%nat ≤ i < n)) as [H1 | H1]; [lia |].
    destruct (decide (i ≤ i < n)) as [H2 | H2]; [| lia].
    rewrite sfence_vma_va_reify. reflexivity.
  - rewrite <- (decide_le_succ i j n Hj (option TlbEntry) (Some (leaf_entry va)) None).
    reflexivity.
Qed.

(* The leader's machine-ghost step on ack i is exactly the IPI deliver + receive:
   deliver core i's IPI, then core i flushes its TLB. *)
Lemma bc_machine_ipi_step (n i : nat) (Hin : i < n) :
  bc_machine root va mem n (i + 1) =
  receive_ipi (deliver_ipi (bc_machine root va mem n i) (Z.of_nat i)) (Z.of_nat i) va.
Proof.
  unfold bc_machine, receive_ipi, deliver_ipi.
  cbn [Machine_cores Machine_mem Machine_ram Machine_ipi].
  rewrite (list_nth_bool_update_self (ipi_prefix n i) i).
  2: { unfold ipi_prefix. rewrite List.length_map. rewrite List.length_seq. lia. }
  rewrite (receive_ipi_cores_true_eq_sfence_at
             (List.map (fun (j : nat) => reify_core root (if decide (i ≤ j < n) then Some (leaf_entry va) else None)) (seq 0 n))
             i va).
  f_equal.
  - apply bc_cores_ipi_step. exact Hin.
  - apply ipi_prefix_step. exact Hin.
Qed.

(* The post-machine's cores are all empty-TLB cores sharing [root]. *)
Lemma bc_cores_done (n : nat) :
  List.map (fun (j : nat) => reify_core root (if decide (n ≤ j < n) then Some (leaf_entry va) else None)) (seq 0 n)
  = List.map (fun _ => core_with_root root) (seq 0 n).
Proof.
  apply List.map_ext_in. intros j Hj.
  apply List.in_seq in Hj.
  rewrite decide_False; [reflexivity |]. lia.
Qed.

(* The reified post-machine satisfies the machine-level conclusion. *)
Lemma bc_post_reifies (n : nat) :
  Forall (fun c => translate c (bc_post_machine root va mem n).(Machine_mem) va = None /\
                   tlb_lookup c va = None)
         (bc_post_machine root va mem n).(Machine_cores).
Proof.
  rewrite /bc_post_machine /bc_machine.
  cbn [Machine_cores Machine_mem].
  rewrite bc_cores_done.
  apply (invalidate_shootdown_empty_cores root va mem n invalid_pte invalid_pte_not_valid).
Qed.

(* The ghost at step i is exactly [ipi_broadcast_cores] applied i times to the
   all-stale, all-undelivered pre-machine. *)
Lemma bc_machine_ipi_cores (n i : nat) (Hi : i ≤ n) :
  bc_machine root va mem n i = ipi_broadcast_cores (bc_machine root va mem n 0) i va.
Proof.
  induction i as [| i' IH].
  - cbn [ipi_broadcast_cores]. reflexivity.
  - cbn [ipi_broadcast_cores].
    assert (Hi' : i' ≤ n) by lia.
    rewrite <- (IH Hi').
    rewrite <- (Nat.add_1_r i').
    apply bc_machine_ipi_step. lia.
Qed.

(* At the end the ghost is the pure IPI broadcast of the pre-machine. *)
Lemma bc_machine_ipi_broadcast (n : nat) :
  bc_machine root va mem n n = ipi_broadcast_cores (bc_machine root va mem n 0) n va.
Proof. apply (bc_machine_ipi_cores n n). lia. Qed.

(* ============================================================
   S2.4 -> S2.3b: the weak-memory post-machine IS the sequential
   IPI-broadcast result, so [ipi_broadcast_correct] applies verbatim.
   ============================================================ *)

(* Core [j] of the step-0 machine still caches [leaf_entry va] (the [0 ≤ j < n]
   guard is always true on [seq 0 n]). *)
Lemma bc_cores_zero (n : nat) :
  List.map (fun (j : nat) => reify_core root (if decide (0%nat ≤ j < n) then Some (leaf_entry va) else None)) (seq 0 n)
  = List.map (fun _ => reify_core root (Some (leaf_entry va))) (seq 0 n).
Proof.
  apply List.map_ext_in. intros j Hj.
  apply List.in_seq in Hj.
  rewrite decide_True; [reflexivity |]. lia.
Qed.

(* After the break-before-make write, the pre-machine is exactly [bc_machine n 0]:
   leaf PTE invalid, every core stale, no IPI delivered. *)
Lemma bc_machine_is_pre_invalidated (n : nat) :
  {| Machine_mem := invalidate_leaf_mem (core_with_root root) mem va invalid_pte;
     Machine_cores := List.map (fun _ => reify_core root (Some (leaf_entry va))) (seq 0 n);
     Machine_ram := [];
     Machine_ipi := ipi_prefix n 0 |}
  = bc_machine root va mem n 0.
Proof.
  unfold bc_machine. f_equal.
  rewrite <- bc_cores_zero. reflexivity.
Qed.

(* [bc_pre_machine] has one IPI bit per core, and every core shares [root]. *)
Lemma bc_pre_machine_len (n : nat) :
  length (bc_pre_machine root va mem n).(Machine_ipi) = length (bc_pre_machine root va mem n).(Machine_cores).
Proof.
  unfold bc_pre_machine. cbn [Machine_ipi Machine_cores].
  unfold ipi_prefix. rewrite !List.length_map. reflexivity.
Qed.

Lemma bc_pre_machine_root (n : nat) :
  Forall (fun c => c.(Core_satp_ppn) = root) (bc_pre_machine root va mem n).(Machine_cores).
Proof.
  unfold bc_pre_machine. cbn [Machine_cores].
  rewrite Forall_map. apply Forall_forall. intros x Hx.
  reflexivity.
Qed.

(* The headline tie: S2.4's post-machine is exactly S2.3b's [ipi_broadcast] of the
   pre-machine (invalidate the leaf PTE, then deliver+receive on every core). *)
Lemma bc_post_machine_is_ipi_broadcast (n : nat) :
  bc_post_machine root va mem n
  = ipi_broadcast (bc_pre_machine root va mem n) root va invalid_pte.
Proof.
  unfold bc_post_machine, bc_pre_machine, ipi_broadcast.
  cbn [Machine_mem Machine_cores Machine_ram Machine_ipi].
  rewrite List.length_map. rewrite List.length_seq.
  rewrite (bc_machine_is_pre_invalidated n).
  exact (bc_machine_ipi_broadcast n).
Qed.

(* The coherence conclusion now follows from S2.3b's [ipi_broadcast_correct] —
   the weak-memory protocol re-establishes the same invariant as the sequential
   IPI broadcast — rather than from a re-derivation. *)
Lemma bc_post_reifies_via_ipi_broadcast (n : nat) :
  Forall (fun c => translate c (bc_post_machine root va mem n).(Machine_mem) va = None /\
                   tlb_lookup c va = None)
         (bc_post_machine root va mem n).(Machine_cores).
Proof.
  rewrite bc_post_machine_is_ipi_broadcast.
  apply (ipi_broadcast_correct (bc_pre_machine root va mem n) root va invalid_pte).
  - apply invalid_pte_not_valid.
  - apply bc_pre_machine_len.
  - apply bc_pre_machine_root.
Qed.

(* ============================================================
   The remote: acquire go, clear tlb, release ack.
   ============================================================ *)

(* A #0 singleton history cannot equal a released history: the latter has a
   #1 write at a time strictly after its #0. *)
Lemma singleton_ne_released (t_i ta0 t1 : positive) (V_i Va0 V1 : view) :
  (ta0 < t1)%positive →
  ({[t_i := (#0, V_i)]} : absHist) ≠ (<[t1 := (#1, V1)]>{[ta0 := (#0, Va0)]} : absHist).
Proof.
  intros Hlt Heq.
  assert (Hlook : (<[t1 := (#1, V1)]>{[ta0 := (#0, Va0)]} : absHist) !! t1 = Some (#1, V1))
    by (apply lookup_insert_eq).
  rewrite <- Heq in Hlook.
  apply lookup_singleton_Some in Hlook as [Hti Hv].
  injection Hv as Hv'. congruence.
Qed.

Lemma bc_remote_spec (γgo : gname) (γtok γack : nat → gname) (go ack tlb : loc) (i n : nat) :
  ∀ (ζgo : absHist) (t_i : positive) (Vgo V_i : view) tid,
  {{{ ⌜i < n⌝ ∗ bc_inv_ctx γgo γtok γack go ack tlb n ∗
      go sy⊒{γgo} ζgo ∗ ⊒Vgo ∗ ⊒V_i ∗
      (ack >> i)%stdpp sw⊒{γack i} {[t_i := (#0, V_i)]} ∗ (tlb >> i)%stdpp ↦ #☠ }}}
    bc_remote_at go ack tlb i @ tid; ⊤
  {{{ RET #☠; True }}}.
Proof.
  iIntros (ζgo t_i Vgo V_i tid Φ) "(%Hi & #HI & #Sgo & #SVgo & #SVi & SWack & Htlb) HΦ".
  rewrite /bc_remote_at /bc_remote.
  wp_lam.
  (* -------- acquire go (repeat until #1) -------- *)
  wp_bind (repeat: !ᵃᶜ(#go))%E.
  iLöb as "IH".
  iApply wp_repeat; [done|].
  iInv (bc_N go) as "INV" "Close". rewrite bc_inv_eq.
  iDestruct "INV" as "[Hgo Hacks]".
  rewrite go_released_eq.
  iDestruct "Hgo" as (ζ t0 t1 V0 V1 Vx) "[>Pts Hpure]".
  iApply (AtomicSeen_acquire_read with "[$Pts $SVgo]"); [solve_ndisj|..].
  { by iApply (AtomicSync_AtomicSeen with "Sgo"). }
  iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Pts)".
  iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & MAX'' & LeV'').
  case (decide (t' = t0)) => [Ht0|NEqt0].
  - subst t'. (* read #0 — keep looping *)
    iAssert (⌜v' = #0⌝)%I as %Eq0.
    { iDestruct "Hpure" as "[%Lt1 %Hζ]".
      iPureIntro.
      rewrite Hζ in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      rewrite lookup_insert_ne in Sub2.
      + rewrite lookup_insert_eq in Sub2. by inversion Sub2.
      + clear -Lt1. intros ?. subst. lia. }
    iMod ("Close" with "[Pts Hpure Hacks]").
    { iIntros "!>". rewrite /bc_inv_def. iFrame "Hacks".
      rewrite go_released_eq. iExists ζ, t0, t1, V0, V1, _. by iFrame "Pts Hpure". }
    iIntros "!>". iExists 0. iSplit; [done|].
    iIntros "!> !>". by iApply ("IH" with "SWack Htlb HΦ").
  - (* read #1 — proceed *)
    iDestruct "Hpure" as "[%Lt1 %Hζ]".
    rewrite Hζ in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
    have Ht1 : t' = t1.
    { case (decide (t' = t1)) => [//|NEqt1].
      exfalso. by rewrite !lookup_insert_ne // in Sub2. }
    subst t'.
    rewrite lookup_insert_eq in Sub2. inversion Sub2. subst v'.
    iMod ("Close" with "[Pts Hacks]").
    { iIntros "!>". rewrite /bc_inv_def. iFrame "Hacks".
      rewrite go_released_eq. iExists ζ, t0, t1, V0, V1, _. iFrame "Pts".
      iPureIntro. split; [exact Lt1|exact Hζ]. }
    iIntros "!>". iExists 1. iSplit; [done|]. iIntros "!> !>". wp_seq.
  (* -------- clear own TLB -------- *)
  wp_op. rewrite Nat2Z.id. wp_write.
  (* -------- release ack (deposit the cleared tlb) -------- *)
  wp_op. rewrite Nat2Z.id.
  iInv (bc_N go) as "INV" "Close". rewrite bc_inv_eq.
  iDestruct "INV" as "[Hgo Hacks]".
  iDestruct (big_sepS_delete _ (all_cores n) i with "Hacks") as "[Hack Hacks_rest]".
  { rewrite elem_of_all_cores. exact Hi. }
  rewrite ack_cell_eq.
  iDestruct "Hack" as (ζa b ta0 Va0 Vax) "[>Ptsa >Own]".
  iDestruct (AtomicPtsTo_AtomicSWriter_agree_1 with "Ptsa SWack") as %->.
  destruct b.
  + (* b = true: impossible — the released history has a #1 write, but the
       concrete writer history is the #0 singleton. *)
    iDestruct "Own" as (tb Vb [Ltb Hb]) "_".
    exfalso. exact (singleton_ne_released t_i ta0 tb V_i Va0 Vb Ltb Hb).
  + (* b = false: the ack cell is still the #0 singleton — release it. *)
    iDestruct "Own" as %Hown0.
    iApply (AtomicSWriter_release_write _ _ _ _ V_i Vax #1
              ((tlb >> i)%stdpp ↦{1} #(encode_tlb None))%I
              with "[$SWack $Ptsa $Htlb $SVi]"); [solve_ndisj|..].
    iIntros "!>" (t1' V1') "(%MAX & SeenV1' & [Htlb SWack'] & Ptsa')".
    iMod ("Close" with "[Hgo Hacks_rest Ptsa' Htlb]"); last first.
    { iIntros "!>". by iApply "HΦ". }
    iIntros "!>". rewrite /bc_inv_def. iSplitL "Hgo"; [done|].
    iApply (big_sepS_delete _ (all_cores n) i).
    { rewrite elem_of_all_cores. exact Hi. }
    rewrite ack_cell_eq. iFrame "Hacks_rest".
    iExists _, true, t_i, V_i, _. iFrame "Ptsa'". iExists t1', V1'. iSplit.
    { iPureIntro. split; [|done]. apply MAX. rewrite lookup_insert_eq. by eexists. }
    iRight. rewrite (flush_tlb_entry_leaf va). by iFrame "Htlb".
Qed.

(* ============================================================
   The leader's ack wait: acquire each ack, advance the machine ghost.
   ============================================================ *)

Lemma bc_wait_all_spec (γgo : gname) (γtok γack : nat → gname) (go ack tlb : loc) :
  ∀ (t : nat → positive) (V : nat → view) (i n : nat) tid,
  {{{ machine_ctx γm (bc_machine root va mem n i) ∗
      bc_inv_ctx γgo γtok γack go ack tlb n ∗
      bc_sync_ctx γack ack t V n }}}
    bc_wait_all_at ack i n @ tid; ⊤
  {{{ RET #☠; machine_ctx γm (bc_post_machine root va mem n) }}}.
Proof.
  iIntros (t V i n tid Φ) "(Hmach & #HI & #Sctx) HΦ".
  rewrite /bc_wait_all_at /bc_wait_all.
  iLöb as "IH" forall (i Φ).
  wp_lam.
  destruct (decide (i < n)) as [Hin | Hnot].
  - (* i < n: acquire ack[i], then recurse *)
    wp_op. rewrite bool_decide_true; [|lia]. wp_if.
    (* the persistent sync-view of ack[i] *)
    iDestruct (big_sepS_elem_of _ (all_cores n) i with "Sctx") as "#[S_i SV_i]".
    { rewrite elem_of_all_cores. exact Hin. }
    (* -------- acquire ack[i] (repeat until #1) -------- *)
    wp_bind (repeat: !ᵃᶜ(#ack +ₗ #i))%E.
    iLöb as "IHack".
    iApply wp_repeat; [done|].
    wp_op. rewrite Nat2Z.id.
    iInv (bc_N go) as "INV" "Close". rewrite bc_inv_eq.
    iDestruct "INV" as "[Hgo Hacks]".
    iDestruct (big_sepS_delete _ (all_cores n) i with "Hacks") as "[Hack Hacks_rest]".
    { rewrite elem_of_all_cores. exact Hin. }
    rewrite ack_cell_eq.
    iDestruct "Hack" as (ζa b ta0 Va0 Vax) "[>Ptsa Own]".
    iApply (AtomicSeen_acquire_read with "[$Ptsa $SV_i]"); [solve_ndisj|..].
    { by iApply (AtomicSync_AtomicSeen with "S_i"). }
    iIntros "!>" (t' v' V' V'' ζ'') "(HF & SV' & SN' & Ptsa)".
    iDestruct "HF" as %([Sub1 Sub2] & Eqt' & MAX' & MAX'' & LeV'').
    case (decide (t' = ta0)) => [Hta0 | NEqta0].
    + (* read #0 — keep looping *)
      subst t'.
      iAssert (⌜v' = #0⌝)%I as %Eq0.
      { destruct b.
        - iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "_".
          iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert_ne in Sub2.
          + rewrite lookup_insert_eq in Sub2. by inversion Sub2.
          + clear -Lt1. intros ?. subst. lia.
        - iDestruct "Own" as %Eqζ'. iPureIntro.
          rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
          rewrite lookup_insert_eq in Sub2. by inversion Sub2. }
      iMod ("Close" with "[Hgo Hacks_rest Ptsa Own]").
      { iIntros "!>". rewrite /bc_inv_def. iSplitL "Hgo"; [done|].
        iApply (big_sepS_delete _ (all_cores n) i).
        { rewrite elem_of_all_cores. exact Hin. }
        rewrite ack_cell_eq. iFrame "Hacks_rest".
        iExists _, b, ta0, Va0, _. iFrame "Ptsa Own". }
      iIntros "!>". iExists 0. iSplit; [done|].
      iIntros "!> !>". by iApply ("IHack" with "Hmach HΦ").
    + (* read #1 — proceed *)
      destruct b; last first.
      { iDestruct "Own" as %Eqζ'. exfalso.
        rewrite Eqζ' in Sub2.
        apply (lookup_weaken _ _ _ _ Eqt'), lookup_singleton_Some in Sub2 as [].
        by apply NEqta0. }
      iClear "IHack".
      iDestruct "Own" as (t1 V1 [Lt1 Eqζ']) "Own".
      rewrite Eqζ' in Sub2. apply (lookup_weaken _ _ _ _ Eqt') in Sub2.
      have ? : t' = t1.
      { case (decide (t' = t1)) => [//|NEqt1].
        exfalso. by rewrite !lookup_insert_ne // in Sub2. }
      subst t'. rewrite lookup_insert_eq in Sub2. inversion Sub2. subst v' V'.
      (* close the invariant, leaving the released ack cell (and its data) as-is *)
      iMod ("Close" with "[Hgo Hacks_rest Ptsa Own]").
      { iIntros "!>". rewrite /bc_inv_def. iSplitL "Hgo"; [done|].
        iApply (big_sepS_delete _ (all_cores n) i).
        { rewrite elem_of_all_cores. exact Hin. }
        rewrite ack_cell_eq. iFrame "Hacks_rest".
        iExists _, true, ta0, Va0, _. iFrame "Ptsa".
        iExists t1, V1. iSplit.
        { iPureIntro. split; [exact Lt1 | exact Eqζ']. }
        iFrame "Own". }
      iIntros "!>". iExists 1. iSplit; [done|]. iIntros "!> !>". wp_seq.
      (* core i has acked (cleared its TLB): the ghost step is literally S2.3's
         [receive_ipi (deliver_ipi _ (Z.of_nat i)) (Z.of_nat i) va], not a bare
         [machine_ctx_update] between arbitrary [bc_machine n i] states. *)
      iMod (machine_ctx_update γm (bc_machine root va mem n i)
              (receive_ipi (deliver_ipi (bc_machine root va mem n i) (Z.of_nat i)) (Z.of_nat i) va)
              with "Hmach") as "Hmach'".
      iAssert (machine_ctx γm (bc_machine root va mem n (i + 1)%nat)) with "[Hmach']" as "Hmach''".
      { rewrite (bc_machine_ipi_step n i Hin). iFrame "Hmach'". }
      wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
      iApply ("IH" $! (i + 1)%nat Φ with "Hmach'' HΦ").
  - (* i ≥ n: return *)
    iMod (machine_ctx_update γm (bc_machine root va mem n i) (bc_post_machine root va mem n)
            with "Hmach") as "Hmach'".
    wp_op. rewrite bool_decide_false; [|lia]. wp_if.
    by iApply ("HΦ" with "Hmach'").
Qed.

(* ============================================================
   Pure helpers shared by the setup / forking proofs.
   ============================================================ *)

Lemma singleton_notin_diff (n i : nat) (Hin : i < n) :
  {[i]} ## (all_cores n ∖ all_cores (i + 1)).
Proof.
  intros x. rewrite elem_of_singleton. intros ->.
  intros Hx. apply elem_of_difference in Hx as [_ Hx]. apply Hx.
  rewrite elem_of_all_cores. lia.
Qed.

(* [new [n]] gives [l ↦∗ repeat v n]; this unfolds it to a per-cell [∗ set] over
   [all_cores n], the form the loop specs consume. *)
Lemma own_loc_na_vec_repeat_all_cores (l : loc) (v : val) (n : nat) :
  l ↦∗ repeat v n ⊢ [∗ set] j ∈ all_cores n, (l >> j) ↦ v.
Proof.
  iIntros "H".
  iDestruct (own_loc_na_vec_repeat l 1 n v with "H") as "H".
  rewrite /all_cores -big_sepS_list_to_set; [done | apply NoDup_seq].
Qed.

(* The i = 0 base cases of the loop specs consume [all_cores n ∖ all_cores 0],
   but the broadcast builds its [∗ set] resources over the whole [all_cores n];
   bridge here (on the hypothesis, where a bare [rewrite] cannot reach it). *)
Lemma big_sepS_all_cores_n_diff_0 (P : nat → vProp) (n : nat) :
  ([∗ set] j ∈ all_cores n, P j) ⊢ ([∗ set] j ∈ all_cores n ∖ all_cores 0, P j).
Proof. by rewrite -all_cores_n_diff_0. Qed.

(* Convert a finite set of NA cells to atomic cells, one fresh gname per cell.
   [AtomicPtsTo_from_na] allocates a fresh gname each call, so the resulting
   γ/t/V functions are injective on S and the sw⊒/sw↦ histories never collide. *)
Lemma big_sepS_atomic_from_na (l : loc) (v : val) (S : gset nat) :
  ([∗ set] j ∈ S, (l >> j) ↦ v)%I ⊢
  |==> ∃ (γ : nat → gname) (t : nat → positive) (V : nat → view),
    [∗ set] j ∈ S, ((l >> j) sw⊒{γ j} {[t j := (v, V j)]} ∗
                    (l >> j) sw↦{γ j} {[t j := (v, V j)]} ∗
                    ⊒(V j)).
Proof.
  apply (set_ind_L (λ S, ([∗ set] j ∈ S, (l >> j) ↦ v)%I ⊢
                         |==> ∃ (γ : nat → gname) (t : nat → positive) (V : nat → view),
                           [∗ set] j ∈ S, ((l >> j) sw⊒{γ j} {[t j := (v, V j)]} ∗
                                           (l >> j) sw↦{γ j} {[t j := (v, V j)]} ∗
                                           ⊒(V j)))).
  - rewrite !big_sepS_empty. iIntros "_". iModIntro.
    iExists (fun _ => 1%positive), (fun _ => 1%positive), (fun _ => ∅).
    rewrite !big_sepS_empty. done.
  - intros i S' Hi IH. iIntros "H".
    rewrite big_sepS_union; last first.
    { intros x. rewrite elem_of_singleton. intros ->. exact Hi. }
    rewrite big_sepS_singleton.
    iDestruct "H" as "[Hi0 HS']".
    iMod (IH with "HS'") as (γ' t' V') "Hres".
    iMod (AtomicPtsTo_from_na (l >> i) v with "Hi0") as (γi ti Vi) "(#SVi & SWi & Ptsi)".
    iIntros "!>".
    iExists (fun j => if decide (j = i) then γi else γ' j),
            (fun j => if decide (j = i) then ti else t' j),
            (fun j => if decide (j = i) then Vi else V' j).
    rewrite big_sepS_union; last first.
    { intros x. rewrite elem_of_singleton. intros ->. exact Hi. }
    rewrite big_sepS_singleton.
    iSplitL "SWi Ptsi SVi".
    { rewrite !decide_True; [|reflexivity..]. iFrame "SWi Ptsi SVi". }
    iApply (big_sepS_mono (λ j, ((l >> j) sw⊒{γ' j} {[t' j := (v, V' j)]} ∗
                                 (l >> j) sw↦{γ' j} {[t' j := (v, V' j)]} ∗
                                 ⊒(V' j))%I)
                         (λ j, ((l >> j) sw⊒{(fun k => if decide (k = i) then γi else γ' k) j}
                                          {[(fun k => if decide (k = i) then ti else t' k) j :=
                                            (v, (fun k => if decide (k = i) then Vi else V' k) j)]} ∗
                                (l >> j) sw↦{(fun k => if decide (k = i) then γi else γ' k) j}
                                          {[(fun k => if decide (k = i) then ti else t' k) j :=
                                            (v, (fun k => if decide (k = i) then Vi else V' k) j)]} ∗
                                ⊒((fun k => if decide (k = i) then Vi else V' k) j))%I)
             with "Hres").
    iIntros (j Hj).
    rewrite !decide_False; [done| | |]; intros ->; apply Hi, Hj.
Qed.

(* ============================================================
   The ack-array initialisation: write #0 to each ack cell (NA).
   ============================================================ *)

Lemma bc_init_acks_spec (ack : loc) :
  ∀ (i n : nat) tid,
  {{{ [∗ set] j ∈ (all_cores n ∖ all_cores i), (ack >> j) ↦ #☠ }}}
    bc_init_acks_at ack i n @ tid; ⊤
  {{{ RET #☠; [∗ set] j ∈ (all_cores n ∖ all_cores i), (ack >> j) ↦ #0 }}}.
Proof.
  iIntros (i n tid Φ) "Hack HΦ".
  rewrite /bc_init_acks_at /bc_init_acks.
  iLöb as "IH" forall (i Φ).
  wp_lam.
  destruct (decide (i < n)) as [Hin | Hnot].
  - wp_op. rewrite bool_decide_true; [|lia]. wp_if.
    rewrite (all_cores_step n i Hin).
    rewrite big_sepS_union; last first.
    { apply singleton_notin_diff. exact Hin. }
    rewrite big_sepS_singleton.
    iDestruct "Hack" as "[Hacki Hackrest]".
    wp_op. rewrite Nat2Z.id. wp_write.
    wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
    iApply ("IH" $! (i + 1)%nat Φ with "Hackrest").
    iIntros "!> Hackrest'".
    iApply "HΦ".
    rewrite big_sepS_union; last first.
    { apply singleton_notin_diff. exact Hin. }
    rewrite big_sepS_singleton. iFrame.
  - wp_op. rewrite bool_decide_false; [|lia]. wp_if.
    rewrite (all_cores_diff_empty n i); [|lia].
    rewrite big_sepS_empty. by iApply "HΦ".
Qed.

(* ============================================================
   The forking loop: spawn remote j for j = i .. n-1.
   ============================================================ *)

Lemma bc_fork_remotes_spec (γgo : gname) (γtok γack : nat → gname) (go ack tlb : loc) :
  ∀ (t : nat → positive) (V : nat → view) (ζgo : absHist) (Vgo : view) (i n : nat) tid,
  {{{ bc_inv_ctx γgo γtok γack go ack tlb n ∗
      bc_sync_ctx γack ack t V n ∗
      go sy⊒{γgo} ζgo ∗ ⊒Vgo ∗
      [∗ set] j ∈ (all_cores n ∖ all_cores i),
        (ack >> j) sw⊒{γack j} {[t j := (#0, V j)]} ∗ (tlb >> j) ↦ #☠ }}}
    bc_fork_remotes_at go ack tlb i n @ tid; ⊤
  {{{ RET #☠; True }}}.
Proof.
  iIntros (t V ζgo Vgo i n tid Φ) "(#HI & #Sctx & #Sgo & #SVgo & Hrest) HΦ".
  rewrite /bc_fork_remotes_at /bc_fork_remotes /bc_remote.
  iLöb as "IH" forall (i Φ).
  wp_lam.
  destruct (decide (i < n)) as [Hin | Hnot].
  - wp_op. rewrite bool_decide_true; [|lia]. wp_if.
    rewrite (all_cores_step n i Hin).
    rewrite big_sepS_union; last first.
    { apply singleton_notin_diff. exact Hin. }
    rewrite big_sepS_singleton.
    iDestruct "Hrest" as "[Hrest_i Hrest']".
    iDestruct "Hrest_i" as "[SWack_i Htlb_i]".
    iDestruct (big_sepS_elem_of _ (all_cores n) i with "Sctx") as "#[_ SV_i]".
    { rewrite elem_of_all_cores. exact Hin. }
    wp_apply (wp_fork with "[SWack_i Htlb_i]"); [done|..].
    + iIntros "!>" (tid').
      iApply (bc_remote_spec γgo γtok γack go ack tlb i n ζgo (t i) Vgo (V i) tid'
                with "[$HI $Sgo $SVgo $SV_i $SWack_i $Htlb_i]").
      { iPureIntro. exact Hin. }
      iIntros "!> _". done.
    + iIntros "_". wp_seq.
      wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
      iApply ("IH" $! (i + 1)%nat Φ with "Hrest'").
      iIntros "!> _". by iApply "HΦ".
  - wp_op. rewrite bool_decide_false; [|lia]. wp_if.
    by iApply "HΦ".
Qed.

(* ============================================================
   The broadcast: allocate, write, convert, fork, wait, reify.
   ============================================================ *)

(* Convert the ack array (already written #0) into per-cell atomic resources:
   the empty ack cell (for the invariant), the writer-seen (for the fork), and
   the sync view (persistent, for the leader).  [γtok] is a parameter because the
   broadcast's remotes deposit the cleared TLB (never the one-shot token), so the
   token itself is never allocated. *)
Lemma bc_ack_setup (ack tlb : loc) (γtok : nat → gname) (n : nat) :
  ([∗ set] j ∈ all_cores n, (ack >> j) ↦ #0)%I ⊢
  |==> ∃ (γack : nat → gname) (t : nat → positive) (V : nat → view),
    [∗ set] j ∈ all_cores n,
      ((ack_cell (ack >> j) (tlb >> j) (γtok j) (γack j) ∗
        (ack >> j) sw⊒{γack j} {[t j := (#0, V j)]}) ∗
       ((ack >> j) sy⊒{γack j} {[t j := (#0, V j)]} ∗ ⊒(V j))).
Proof.
  iIntros "Hack".
  iMod (big_sepS_atomic_from_na ack #0 (all_cores n) with "Hack") as (γack t V) "HAtom".
  iIntros "!>". iExists γack, t, V.
  iApply (big_sepS_mono
    (λ j, ((ack >> j) sw⊒{γack j} {[t j := (#0, V j)]} ∗
           (ack >> j) sw↦{γack j} {[t j := (#0, V j)]} ∗ ⊒(V j))%I)
    (λ j, ((ack_cell (ack >> j) (tlb >> j) (γtok j) (γack j) ∗
            (ack >> j) sw⊒{γack j} {[t j := (#0, V j)]}) ∗
           ((ack >> j) sy⊒{γack j} {[t j := (#0, V j)]} ∗ ⊒(V j)))%I)
    (all_cores n) with "HAtom").
  iIntros (j Hj) "(SW & Pts & SeenV)".
  iDestruct (AtomicSWriter_AtomicSync with "SW") as "#S".
  iDestruct (view_at_intro with "Pts") as (Vx) "[_ Pts]".
  rewrite ack_cell_eq.
  iFrame "SW SeenV S".
  iExists _, false, (t j), (V j), Vx. iFrame "Pts". done.
Qed.

(* [wp_new] is phrased over a [Z] size, so its postcondition mentions the
   roundtrip [Z.to_nat (Z.of_nat n)]; the broadcast allocates its per-core
   arrays at the Coq-nat size [n], so give [new] a nat-phrased spec instead.
   The two roundtrip lemmas below are the only place the [Z.of_nat]/[Z.to_nat]
   impedance mismatch is bridged. *)

Lemma repeat_poison_roundtrip (n : nat) :
  repeat #☠ (Z.to_nat (Z.of_nat n)) = repeat #☠ n.
Proof. f_equal. apply Nat2Z.id. Qed.

Lemma seq_roundtrip (n : nat) :
  seq 0 (Z.to_nat (Z.of_nat n)) = seq 0 n.
Proof. f_equal. apply Nat2Z.id. Qed.

Lemma own_loc_na_vec_poison_roundtrip (l : loc) (n : nat) :
  l ↦∗ repeat #☠ (Z.to_nat (Z.of_nat n)) -∗ l ↦∗ repeat #☠ n.
Proof.
  rewrite repeat_poison_roundtrip. iIntros "$".
Qed.

Lemma big_sepL_seq_poison_roundtrip (l : loc) (n : nat) :
  ([∗ list] i ∈ seq 0 (Z.to_nat (Z.of_nat n)), meta_token (l >> i) ⊤) -∗
  ([∗ list] i ∈ seq 0 n, meta_token (l >> i) ⊤).
Proof.
  rewrite seq_roundtrip. iIntros "$".
Qed.

Lemma wp_new_nat (n : nat) :
  ∀ tid,
  {{{ True }}} new [ #(Z.of_nat n) ] @ tid; ⊤
  {{{ l, RET LitV $ LitLoc l;
      (⎡†l…n⎤ ∨ ⌜n = 0%nat⌝) ∗
      l ↦∗ repeat #☠ n ∗
      [∗ list] i ∈ seq 0 n, meta_token (l >> i) ⊤ }}}.
Proof.
  iIntros (tid Φ) "_ HΦ". wp_lam. wp_op; case_bool_decide.
  - wp_if. assert (n = 0%nat) as -> by lia. iApply "HΦ".
    rewrite own_loc_na_vec_nil. auto.
  - wp_if. wp_alloc l as "Htok" "Hvec" "Hfree"; first lia.
    apply Nat2Z.inj in Hsz. subst sz.
    iApply "HΦ".
    iFrame "Hfree".
    iSplitL "Hvec".
    { iApply (own_loc_na_vec_poison_roundtrip with "Hvec"). }
    iApply (big_sepL_seq_poison_roundtrip with "Htok").
Qed.

Lemma bc_broadcast_spec (n : nat) :
  ∀ tid,
  {{{ machine_ctx γm (broadcast_pre_machine root va mem n) }}}
    bc_broadcast_at n @ tid; ⊤
  {{{ RET #☠; ∃ (γgo : gname) (γtok γack : nat → gname) (pte go ack tlb : loc),
      bc_inv_ctx γgo γtok γack go ack tlb n ∗
      pte ↦ #(encode_pte invalid_pte) ∗
      machine_ctx γm (bc_post_machine root va mem n) }}}.
Proof.
  iIntros (tid Φ) "Hm0 HΦ".
  rewrite /bc_broadcast_at /bc_broadcast.
  cbn beta.
  wp_apply wp_new; [done..|]. iIntros (pte) "(_ & Hpte & _)".
  rewrite own_loc_na_vec_singleton.
  wp_let.
  wp_apply wp_new; [done..|]. iIntros (go) "(_ & Hgo & _)".
  rewrite own_loc_na_vec_singleton.
  wp_let.
  wp_apply (wp_new_nat n tid); [done..|]. iIntros (ack) "(_ & Hack & _)".
  wp_let.
  wp_apply (wp_new_nat n tid); [done..|]. iIntros (tlb) "(_ & Htlb & _)".
  wp_let.
  (* ---- break-before-make: go <- #0, pte <- invalid ---- *)
  wp_op. rewrite shift_0. wp_write.
  wp_op. rewrite shift_0. wp_write.
  iMod (machine_ctx_update γm (broadcast_pre_machine root va mem n)
          (bc_machine root va mem n 0) with "Hm0") as "Hm1".
  (* ---- go: NA -> atomic, then release ---- *)
  iMod (AtomicPtsTo_from_na with "Hgo") as (γgo tgo Vgo) "(#SeenVgo & SWgo & Ptsgo)".
  iDestruct (AtomicSWriter_AtomicSync with "SWgo") as "#Sgo".
  iDestruct (view_at_intro with "Ptsgo") as (Vxgo) "[_ Ptsgo]".
  wp_op. rewrite shift_0.
  wp_apply (AtomicSWriter_release_write _ _ _ _ Vgo Vxgo #1 True%I
              with "[$SWgo $Ptsgo $SeenVgo]"); [solve_ndisj|..].
  iIntros (t1 V1) "(%MAX & _ & [_ SWgo'] & Ptsgo')".
  iAssert (go_released go γgo)%I with "[Ptsgo']" as "Hgo_released".
  { rewrite go_released_eq. iExists _, tgo, t1, Vgo, V1, _. iFrame "Ptsgo'".
    iPureIntro. split; [|done]. destruct MAX as [Hfresh _]. apply Hfresh.
    rewrite lookup_insert_eq. by eexists. }
  wp_seq.
  (* ---- ack array: write #0, then convert to atomic cells ---- *)
  iDestruct (own_loc_na_vec_repeat_all_cores ack #☠ n with "Hack") as "HackNA".
  rewrite all_cores_n_diff_0.
  wp_apply (bc_init_acks_spec ack 0 n tid with "HackNA").
  iIntros "Hack0".
  wp_seq.
  rewrite -all_cores_n_diff_0.
  iMod (bc_ack_setup ack tlb (fun _ => γgo) n with "Hack0") as (γack t V) "HackAll".
  iDestruct (big_sepS_sep (λ j, (ack_cell (ack >> j) (tlb >> j) (γgo) (γack j) ∗
                                   (ack >> j) sw⊒{γack j} {[t j := (#0, V j)]})%I)
                         (λ j, ((ack >> j) sy⊒{γack j} {[t j := (#0, V j)]} ∗ ⊒(V j))%I)
                         (all_cores n) with "HackAll") as "[HackSW #Sctx]".
  iDestruct (big_sepS_sep (λ j, ack_cell (ack >> j) (tlb >> j) (γgo) (γack j))%I
                         (λ j, (ack >> j) sw⊒{γack j} {[t j := (#0, V j)]})%I
                         (all_cores n) with "HackSW") as "[HackCells Hack_sw]".
  (* ---- establish the invariant ---- *)
  iMod (inv_alloc (bc_N go) _ (bc_inv γgo (fun _ => γgo) γack go ack tlb n)
          with "[Hgo_released HackCells]") as "#HI".
  { rewrite bc_inv_eq. iIntros "!>". iFrame "Hgo_released HackCells". }
  (* ---- the fork + wait premises ---- *)
  iDestruct (own_loc_na_vec_repeat_all_cores tlb #☠ n with "Htlb") as "HtlbNA".
  iDestruct (big_sepS_sep_2 _ _ (all_cores n) with "Hack_sw HtlbNA") as "Hrest".
  iDestruct (big_sepS_all_cores_n_diff_0
              (λ j, ((ack >> j) sw⊒{γack j} {[t j := (#0, V j)]} ∗ (tlb >> j) ↦ #☠)%I) n
              with "Hrest") as "Hrest0".
  wp_apply (bc_fork_remotes_spec γgo (fun _ => γgo) γack go ack tlb
              t V {[tgo := (#0, Vgo)]} Vgo 0 n tid
              with "[$HI $Sctx $Sgo $SeenVgo $Hrest0]").
  iIntros "_".
  wp_seq.
  wp_apply (bc_wait_all_spec γgo (fun _ => γgo) γack go ack tlb t V 0 n tid
              with "[$Hm1 $HI $Sctx]").
  iIntros "Hm".
  iApply "HΦ".
  iExists γgo, (fun _ => γgo), γack, pte, go, ack, tlb. iFrame "HI Hpte Hm".
Qed.

End bc_inv.

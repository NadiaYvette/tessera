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

(* Application helpers: the [ # ] literal notation does not survive the list
   application (it binds to the head via the App coercion), so we write the
   literal arguments explicitly. *)
Definition bc_remote_at (go ack tlb : loc) (i : nat) : expr :=
  App bc_remote [Lit (LitLoc go); Lit (LitLoc ack); Lit (LitLoc tlb); Lit (LitInt (Z.of_nat i))].
Definition bc_init_acks_at (ack : loc) (n : nat) : expr :=
  App bc_init_acks [Lit (LitLoc ack); Lit (LitInt 0); Lit (LitInt (Z.of_nat n))].
Definition bc_fork_remotes_at (go ack tlb : loc) (i n : nat) : expr :=
  App bc_fork_remotes [Lit (LitLoc go); Lit (LitLoc ack); Lit (LitLoc tlb);
                       Lit (LitInt (Z.of_nat i)); Lit (LitInt (Z.of_nat n))].
Definition bc_wait_all_at (ack : loc) (i n : nat) : expr :=
  App bc_wait_all [Lit (LitLoc ack); Lit (LitInt (Z.of_nat i)); Lit (LitInt (Z.of_nat n))].
Definition bc_broadcast_at (n : nat) : expr :=
  App bc_broadcast [Lit (LitInt (Z.of_nat n))].

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

(* The leader's persistent reader context: the SyncSeen view of each ack cell
   (a #0 singleton at [t j]) plus the SeenView of its allocation view [V j].
   Derived once from AtomicPtsTo_from_na in the broadcast setup and shared with
   every wait/read. *)
Definition bc_sync_ctx (γack : nat → gname) (ack : loc)
                       (t : nat → positive) (V : nat → view) (n : nat) : vProp :=
  [∗ set] j ∈ all_cores n,
    ((ack >> j)%stdpp sy⊒{γack j} {[t j := (#0, V j)]} ∗ ⊒(V j))%I.

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

Lemma bc_machine_done_ge (n i : nat) :
  n ≤ i → bc_machine root va mem n i = broadcast_post_machine root va mem n.
Proof.
  intros Hni. rewrite /bc_machine /broadcast_post_machine /reify_machine.
  f_equal. apply List.map_ext_in. intros j Hj.
  apply list_elem_of_In in Hj. apply elem_of_seq in Hj.
  rewrite decide_False; [done|]. lia.
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
    iRight. by iFrame "Htlb".
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
  {{{ RET #☠; machine_ctx γm (broadcast_post_machine root va mem n) }}}.
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
      (* core i has acked (cleared its TLB): advance the machine ghost *)
      iMod (machine_ctx_update γm (bc_machine root va mem n i) (bc_machine root va mem n (i + 1))
              with "Hmach") as "Hmach'".
      wp_op. replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
      iApply ("IH" $! (i + 1)%nat Φ with "Hmach' HΦ").
  - (* i ≥ n: return *)
    iMod (machine_ctx_update γm (bc_machine root va mem n i) (broadcast_post_machine root va mem n)
            with "Hmach") as "Hmach'".
    wp_op. rewrite bool_decide_false; [|lia]. wp_if.
    by iApply ("HΦ" with "Hmach'").
Qed.

End bc_inv.

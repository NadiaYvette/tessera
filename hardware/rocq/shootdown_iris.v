(* Tessera — Stage 2, S2.1: the concurrent N-core broadcast shootdown in Iris
   HeapLang, over the concrete generated machine. See ../../doc/stage2-shootdown.md.

   HeapLang's `val` is fixed, so the concrete `Pte` / `option TlbEntry` are encoded
   as `val` (nested pairs / sums over integer literals); the encode/decode inverses
   are proved here as the pure foundation. The protocol + invariant follow. *)

From iris.heap_lang Require Import lang notation.
From stdpp Require Import bitvector.definitions.
From Stdlib Require Import ZArith.
From SailStdpp Require Import MachineWord.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import coherence_leaf. (* invalidate_leaf_mem / leaf_addr *)
Require Import shootdown. (* core_with_root / invalidate_shootdown / invalidate_shootdown_correct *)
Import ListNotations.

(* ============================================================
   Concrete-value encoding.
   ============================================================ *)

Definition b2z (b : bool) : Z := if b then 1 else 0.
Definition z2b (z : Z) : bool := Z.eqb z 1.

Lemma z2b_b2z (b : bool) : z2b (b2z b) = b.
Proof. destruct b; reflexivity. Qed.

(* The bitvector fields travel as their unsigned value (int_of_mword false),
   rebuilt with mword_of_int.  The roundtrip needs no bit arithmetic beyond
   stdpp's Z_to_bv_bv_unsigned (and bv_unsigned_in_range for positivity). *)
Lemma mword_of_int_int_of_mword {n : Z} (w : mword n) :
  mword_of_int (int_of_mword false w) = w.
Proof.
  unfold mword_of_int, int_of_mword, get_word.
  unfold MachineWord.Z_to_word, MachineWord.word_to_N.
  rewrite Z2N.id.
  { apply Z_to_bv_bv_unsigned. }
  { destruct (bv_unsigned_in_range _ w) as [H0 _]; exact H0. }
Qed.

(* Pte -> val: nested pairs (valid, read, write, exec, user, ppn-as-Z). *)
Definition encode_pte (p : Pte) : val :=
  PairV (#(b2z p.(Pte_valid)))
  (PairV (#(b2z p.(Pte_read)))
  (PairV (#(b2z p.(Pte_write)))
  (PairV (#(b2z p.(Pte_exec)))
  (PairV (#(b2z p.(Pte_user))) #(int_of_mword false p.(Pte_ppn)))))).

Definition decode_pte (v : val) : option Pte :=
  match v with
  | PairV (LitV (LitInt z0))
      (PairV (LitV (LitInt z1))
        (PairV (LitV (LitInt z2))
          (PairV (LitV (LitInt z3))
            (PairV (LitV (LitInt z4)) (LitV (LitInt z5)))))) =>
      Some {| Pte_valid := z2b z0; Pte_read := z2b z1; Pte_write := z2b z2;
              Pte_exec := z2b z3; Pte_user := z2b z4; Pte_ppn := mword_of_int z5 |}
  | _ => None
  end.

Lemma decode_pte_encode (p : Pte) : decode_pte (encode_pte p) = Some p.
Proof.
  destruct p as [v r w e u ppn]. cbn.
  rewrite !z2b_b2z. rewrite mword_of_int_int_of_mword. reflexivity.
Qed.

(* option TlbEntry -> val: InjLV #() for None, InjRV (vpn, ppn, perm) for Some. *)
Definition encode_tlb (o : option TlbEntry) : val :=
  match o with
  | None => InjLV #()
  | Some e => InjRV (PairV (#(int_of_mword false e.(TlbEntry_vpn)))
                           (PairV (#(int_of_mword false e.(TlbEntry_ppn)))
                                  #(num_of_Perm e.(TlbEntry_perm))))
  end.

Definition decode_tlb (v : val) : option (option TlbEntry) :=
  match v with
  | InjLV (LitV LitUnit) => Some None
  | InjRV (PairV (LitV (LitInt zv)) (PairV (LitV (LitInt zp)) (LitV (LitInt zperm)))) =>
      Some (Some {| TlbEntry_vpn := mword_of_int zv; TlbEntry_ppn := mword_of_int zp;
                    TlbEntry_perm := Perm_of_num zperm |})
  | _ => None
  end.

Lemma decode_tlb_encode (o : option TlbEntry) : decode_tlb (encode_tlb o) = Some o.
Proof.
  destruct o as [e |]; cbn.
  - destruct e as [vpn ppn perm]. cbn.
    rewrite !mword_of_int_int_of_mword. rewrite Perm_num_of_roundtrip. reflexivity.
  - reflexivity.
Qed.

(* ============================================================
   Concrete values, program, ghost state.
   ============================================================ *)

From iris.algebra Require Import auth gset gmap excl.
From iris.base_logic.lib Require Import invariants ghost_var.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Import par.

Definition invalid_pte : Pte :=
  {| Pte_valid := false; Pte_read := true; Pte_write := true;
     Pte_exec := true; Pte_user := true; Pte_ppn := mword_of_int 0 |}.

Lemma invalid_pte_not_valid : invalid_pte.(Pte_valid) = false.
Proof. reflexivity. Qed.

Definition valid_pte : Pte :=
  {| Pte_valid := true; Pte_read := true; Pte_write := true;
     Pte_exec := true; Pte_user := true; Pte_ppn := mword_of_int 0 |}.

Definition leaf_entry : TlbEntry :=
  {| TlbEntry_vpn := mword_of_int 0; TlbEntry_ppn := mword_of_int 0;
     TlbEntry_perm := ReadWrite |}.

Lemma encode_tlb_Some_ne_None (e : TlbEntry) :
  encode_tlb (Some e) ≠ encode_tlb None.
Proof. intros H. cbn in H. discriminate. Qed.

Definition wait : val :=
  rec: "wait" "y" := if: !"y" then #() else "wait" "y".

Definition wait_cnt : val :=
  rec: "wait_cnt" "cnt" "n" :=
    if: (!"cnt") = "n" then #() else "wait_cnt" "cnt" "n".

Definition remote : val :=
  λ: "tlb" "go" "cnt" "i",
    wait "go" ;;
    ("tlb" +ₗ "i") <- encode_tlb None ;;
    (* Ack counting uses an atomic fetch-and-add: a load+store increment is a
       lost update under weak memory, and a pure binop step cannot run inside
       the [iInv] accessor (its mask-restoring fupd blocks [wp_op]). *)
    FAA "cnt" #1 ;;
    #().

Definition fork_remotes : val :=
  rec: "fork_remotes" "tlb" "go" "cnt" "i" "n" :=
    if: "i" < "n"
    then (Fork (remote "tlb" "go" "cnt" "i") ;;
          "fork_remotes" "tlb" "go" "cnt" ("i" + #1) "n")
    else #().

Definition broadcast : val :=
  λ: "n",
    let: "pte" := ref (encode_pte valid_pte) in
    let: "tlb" := AllocN "n" (encode_tlb (Some leaf_entry)) in
    let: "go"  := ref #false in
    let: "cnt" := ref #0 in
    "pte" <- encode_pte invalid_pte ;;
    "go" <- #true ;;
    fork_remotes "tlb" "go" "cnt" #0 "n" ;;
    wait_cnt "cnt" "n".

Definition all_cores (n : nat) : gset nat := list_to_set (seq 0 n).

(* The pure side-condition of the invariant, hoisted out of `⌜⌝` so the compound
   nat/set arithmetic isn't parsed under `bi_pure`'s `%type%stdpp` scope. *)
Definition sd_pure (n k : nat) (m : gmap nat (exclR unitO)) : Prop :=
  k + size (dom m) = n ∧ dom m ⊆ all_cores n.

(* When the ack counter has reached n, the pending map is empty: every remote has
   acked. These two lemmas are the pure bridge from `sd_pure` to `m = ∅` / `dom m = ∅`. *)
Lemma sd_pure_dom_empty (n : nat) (m : gmap nat (exclR unitO)) :
  sd_pure n n m -> dom m = ∅.
Proof.
  intros [Hsum Hsub]. apply leibniz_equiv. apply size_empty_inv. lia.
Qed.

Lemma sd_pure_done (n : nat) (m : gmap nat (exclR unitO)) :
  sd_pure n n m -> m = ∅.
Proof.
  intros Hpure. apply map_empty. intros i.
  apply not_elem_of_dom. rewrite (sd_pure_dom_empty n m Hpure). set_solver.
Qed.

Lemma all_cores_clear (n : nat) (m : gmap nat (exclR unitO)) :
  dom m = ∅ → all_cores n ∖ dom m = all_cores n.
Proof.
  intros Hdom. rewrite Hdom. apply difference_empty_L.
Qed.

Class sdG Σ := SdG { sd_inG : inG Σ (authR (gmapUR nat (exclR unitO)));
                      sd_tokG : inG Σ (exclR unitO) }.
Local Existing Instances sd_inG sd_tokG.
Definition sdΣ : gFunctors := #[GFunctor (authR (gmapUR nat (exclR unitO))); GFunctor (exclR unitO)].
Global Instance subG_sdΣ {Σ} : subG sdΣ Σ → sdG Σ.
Proof. solve_inG. Qed.

(* Pure pending-map helpers, needed by both the reification bridge below and the
   concurrent proof. *)

Definition pending_map (n : nat) : gmap nat (exclR unitO) :=
  gset_to_gmap (Excl ()) (all_cores n).

Lemma pending_map_valid (n : nat) : ✓ (pending_map n).
Proof.
  intros i. rewrite /pending_map lookup_gset_to_gmap. case_decide; cbn; done.
Qed.

Lemma elem_of_all_cores (n i : nat) : i ∈ all_cores n ↔ i < n.
Proof.
  rewrite /all_cores elem_of_list_to_set elem_of_seq. lia.
Qed.

Lemma dom_pending_map (n : nat) : dom (pending_map n) = all_cores n.
Proof. rewrite /pending_map. apply dom_gset_to_gmap. Qed.

(* ============================================================
   The machine ghost + the reification bridge.
   ============================================================ *)

(* Carries the concrete [Machine] through the broadcast proof so the program's
   postcondition can cite the machine-level coherence conclusion. *)
Class machineG Σ := MachineG { machine_inG : ghost_varG Σ Machine }.
Local Existing Instances machine_inG.
Definition machineΣ : gFunctors := #[ghost_varΣ Machine].
Global Instance subG_machineΣ {Σ} : subG machineΣ Σ → machineG Σ.
Proof. solve_inG. Qed.
Definition machine_ctx `{!machineG Σ} (γm : gname) (m : Machine) : iProp Σ := ghost_var γm 1 m.

(* A core whose TLB is the reification of an [option TlbEntry]: [None] is an
   empty TLB, [Some e] is the singleton [e]. *)
Definition reify_core (root : mword 44) (o : option TlbEntry) : Core :=
  {| Core_satp_ppn := root; Core_tlb := match o with None => [] | Some e => [e] end |}.

(* Reconstructs the machine the broadcast program models: memory whose leaf PTE
   for `va` is `p` (written via the data-dependent walk), and n cores sharing
   `root` whose TLBs are reified from `tls`. *)
Definition reify_machine (root : mword 44) (va : mword 64) (mem : list MemEntry)
                        (p : Pte) (tls : nat → option TlbEntry) (n : nat) : Machine :=
  {| Machine_mem := invalidate_leaf_mem (core_with_root root) mem va p;
     Machine_cores := List.map (fun j => reify_core root (tls j)) (seq 0 n) |}.

(* Core [j] still caches the stale [leaf_entry] exactly while it is pending
   (in the domain of the auth map [m]); once it has acked its TLB is empty. *)
Definition tls_of (m : gmap nat (exclR unitO)) (j : nat) : option TlbEntry :=
  if decide (j ∈ dom m) then Some leaf_entry else None.

(* The machine the broadcast program models before/after the shootdown. *)
Definition broadcast_pre_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) : Machine :=
  reify_machine root va mem valid_pte (fun _ => Some leaf_entry) n.

Definition broadcast_post_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) : Machine :=
  reify_machine root va mem invalid_pte (fun _ => None) n.

(* [tls_of (pending_map n)] agrees with the constant [Some leaf_entry] on the
   core range [0..n), so the invariant's machine coincides with the pre-machine. *)
Lemma tls_of_pending_map (n j : nat) :
  j < n → tls_of (pending_map n) j = Some leaf_entry.
Proof.
  intros Hj. rewrite /tls_of. apply decide_True.
  rewrite dom_pending_map. apply elem_of_all_cores. done.
Qed.

Lemma reify_machine_tls_of_pending (root : mword 44) (va : mword 64) (mem : list MemEntry)
                                   (p : Pte) (n : nat) :
  reify_machine root va mem p (tls_of (pending_map n)) n =
  reify_machine root va mem p (fun _ => Some leaf_entry) n.
Proof.
  unfold reify_machine. f_equal.
  apply List.map_ext_in. intros j Hj.
  apply list_elem_of_In in Hj. apply elem_of_seq in Hj.
  rewrite (tls_of_pending_map n j); [reflexivity | lia].
Qed.

(* The reified post-machine (every TLB cleared, leaf PTE invalid) satisfies the
   machine-level conclusion, citing `invalidate_shootdown_empty_cores`. *)
Lemma broadcast_reifies_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) :
  Forall (fun c => translate c (broadcast_post_machine root va mem n).(Machine_mem) va = None /\
                   tlb_lookup c va = None)
         (broadcast_post_machine root va mem n).(Machine_cores).
Proof.
  apply (invalidate_shootdown_empty_cores root va mem n invalid_pte invalid_pte_not_valid).
Qed.

(* ============================================================
   The concurrent proof.
   ============================================================ *)

Lemma size_dom_delete {A} `{Countable A} (m : gmap A (exclR unitO)) (i : A) :
  i ∈ dom m → size (dom (delete i m)) = size (dom m) - 1.
Proof.
  intros Hi. rewrite !size_dom. rewrite map_size_delete_Some.
  - lia.
  - apply elem_of_dom. done.
Qed.

Section proof.
  Context `{!heapGS Σ, !spawnG Σ, !sdG Σ, !machineG Σ}.
  Context (γm : gname) (root : mword 44) (va : mword 64) (mem : list MemEntry).
  Let N := nroot .@ "sd".

  (* Single-phase invariant: it is only ever established AFTER the leader sets
     go := true (before that the leader holds everything locally), so `go ↦ #true`
     is fixed and there is no `b` case-split to reason about. The machine ghost is
     derived from the pending map [m]: a core caches [leaf_entry] exactly while it
     is pending, and the leaf PTE is fixed invalid from the break-before-make
     write onward — so the ghost tracks the heap faithfully. *)
  Definition sd_inv (γ γtok : gname) (tlb go cnt : loc) (n : nat) : iProp Σ :=
    (∃ (m : gmap nat (exclR unitO)) (k : nat),
       go ↦ #true ∗
       cnt ↦ #k ∗
       own γ (● m) ∗
       ((machine_ctx γm (reify_machine root va mem invalid_pte (tls_of m) n) ∗
         ([∗ set] j ∈ (all_cores n ∖ dom m), (tlb +ₗ Z.of_nat j) ↦ encode_tlb None))
        ∨ (own γtok (Excl ()) ∗ ⌜ m = ∅ ⌝)) ∗
       ⌜ sd_pure n k m ⌝)%I.

Lemma pending_token_delete γ (m : gmap nat (exclR unitO)) (i : nat) :
  own γ (● m) -∗ own γ (◯ {[i := Excl ()]}) ==∗ own γ (● (delete i m)).
Proof.
  iIntros "Hm Hi".
  iMod (own_update_2 with "Hm Hi") as "H".
  { apply auth_update. apply delete_singleton_local_update. apply excl_exclusive. }
  iDestruct (own_op with "H") as "[Hm _]".
  by iFrame.
Qed.

  (* -------- ghost helpers: pending_map = big_opS, fragment splitting -------- *)

  Lemma auth_frag_gset_to_gmap {A : cmra} `{Countable K} (x : A) (S : gset K) :
    ◯ (gset_to_gmap x S) ≡ [^op set] j ∈ S, ◯ {[j := x]}.
  Proof.
    apply (set_ind_L (λ S, ◯ (gset_to_gmap x S) ≡ [^op set] j ∈ S, ◯ {[j := x]})).
    - cbn. rewrite /auth_frag /view_frag.
      rewrite gset_to_gmap_empty big_opS_empty. reflexivity.
    - intros i X Hi IH.
      rewrite gset_to_gmap_union_singleton.
      rewrite insert_singleton_op; [| apply lookup_gset_to_gmap_None, Hi].
      rewrite auth_frag_op big_opS_insert; [| exact Hi].
      by rewrite IH.
  Qed.

  Lemma pending_tokens_split γ n :
    own γ (◯ (pending_map n)) ⊢ [∗ set] j ∈ all_cores n, own γ (◯ {[j := Excl ()]}).
  Proof.
    rewrite /pending_map.
    setoid_rewrite (auth_frag_gset_to_gmap (A := exclR unitO) (Excl ()) (all_cores n)).
    apply big_opS_own_1.
  Qed.

  (* -------- the wait loop -------- *)

  (* `go` is fixed true in the invariant, so the wait is a single load. *)
  Lemma wait_spec (γ γtok : gname) (tlb go cnt : loc) (n : nat) :
    {{{ inv N (sd_inv γ γtok tlb go cnt n) }}}
      wait #go
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "#HI HΦ".
    wp_rec.
    wp_bind (! #go)%E.
    iInv "HI" as (m k) "(>Hgo & >Hcnt & >Hauth & >Htlbor & >%Hpure)" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hgo Hcnt Hauth Htlbor]") as "_".
    { iNext. iExists m, k. iFrame "Hgo Hcnt Hauth Htlbor". iPureIntro. done. }
    iModIntro. wp_pures. by iApply "HΦ".
  Qed.

  (* -------- the remote's ack: spend the pending token, deposit the cleared TLB -------- *)

  Lemma token_in_dom γ (m : gmap nat (exclR unitO)) (i : nat) :
    own γ (● m) -∗ own γ (◯ {[i := Excl ()]}) -∗ ⌜ i ∈ dom m ⌝.
  Proof.
    iIntros "Hauth Hi".
    iDestruct (own_valid_2 with "Hauth Hi") as %Hvalid.
    apply auth_both_valid_discrete in Hvalid as [Hincl Hvalidm].
    iPureIntro.
    apply elem_of_dom. unfold is_Some.
    pose proof (proj1 (singleton_included_exclusive_l m i (Excl ())
                        (excl_exclusive (Excl ())) Hvalidm) Hincl) as Hlook.
    destruct (Some_equiv_eq (m !! i) (Excl ())) as [Hfwd _].
    destruct (Hfwd Hlook) as (y & Heq & _).
    eauto.
  Qed.

  Lemma ack_dom_step (n i : nat) (m : gmap nat (exclR unitO)) :
    i ∈ dom m → i ∈ all_cores n →
    all_cores n ∖ dom (delete i m) = {[i]} ∪ (all_cores n ∖ dom m).
  Proof.
    intros Him Hall.
    rewrite dom_delete_L.
    apply set_eq. intro x.
    setoid_rewrite elem_of_union.
    setoid_rewrite elem_of_difference.
    setoid_rewrite not_elem_of_difference.
    split.
    - intros [Hxn [Hnd | Hxi]].
      + right. split; [done | done].
      + left. done.
    - intros [Hxi | [Hxn Hnd]].
      + apply elem_of_singleton_1 in Hxi. subst x.
        split; [done | right; apply elem_of_singleton_2; done].
      + split; [done | left; done].
  Qed.

  Lemma remote_ack γ (tlb : loc) (n i : nat) (m : gmap nat (exclR unitO)) :
    i ∈ dom m → i ∈ all_cores n →
    machine_ctx γm (reify_machine root va mem invalid_pte (tls_of m) n) -∗
    own γ (● m) -∗ own γ (◯ {[i := Excl ()]}) -∗
    (tlb +ₗ Z.of_nat i) ↦ encode_tlb None -∗
    ([∗ set] j ∈ (all_cores n ∖ dom m), (tlb +ₗ Z.of_nat j) ↦ encode_tlb None) ==∗
    machine_ctx γm (reify_machine root va mem invalid_pte (tls_of (delete i m)) n) ∗
    own γ (● (delete i m)) ∗
    ([∗ set] j ∈ (all_cores n ∖ dom (delete i m)), (tlb +ₗ Z.of_nat j) ↦ encode_tlb None).
  Proof.
    iIntros (Him Hall) "Hmach Hauth Hi Htlb Hacked".
    iMod (pending_token_delete γ m i with "Hauth Hi") as "Hauth'".
    (* Core i just cleared its TLB: [tls_of] maps it from [Some leaf_entry] to
       [None], so the machine advances to [tls_of (delete i m)]. *)
    iMod (ghost_var_update (reify_machine root va mem invalid_pte (tls_of (delete i m)) n)
                            γm (reify_machine root va mem invalid_pte (tls_of m) n)
            with "Hmach") as "Hmach'".
    iAssert ([∗ set] j ∈ (all_cores n ∖ dom (delete i m)), (tlb +ₗ Z.of_nat j) ↦ encode_tlb None)%I
      with "[Htlb Hacked]" as "Hacked'".
    { rewrite (ack_dom_step n i m Him Hall).
      rewrite big_opS_insert; [| set_solver ].
      iFrame. }
    iModIntro. iFrame "Hmach' Hauth' Hacked'".
  Qed.

  Lemma remote_spec (γ γtok : gname) (tlb go cnt : loc) (n i : nat) :
    {{{ inv N (sd_inv γ γtok tlb go cnt n) ∗
        own γ (◯ {[i := Excl ()]}) ∗ (tlb +ₗ Z.of_nat i) ↦ encode_tlb (Some leaf_entry) }}}
      remote #tlb #go #cnt #i
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#HI & Hi & Htlb) HΦ".
    wp_rec. wp_pures.
    wp_apply (wait_spec γ γtok tlb go cnt n with "[$HI]"); [iIntros "_"].
    wp_pures. wp_store.
    wp_bind (FAA #cnt #1)%E.
    iInv "HI" as (m k) "(>Hgo & >Hcnt & >Hauth & >Htlbor & >%Hpure)" "Hclose".
    wp_faa.
    iDestruct (token_in_dom with "Hauth Hi") as %Him.
    destruct Hpure as [Hsum Hsub].
    assert (Hall : i ∈ all_cores n) by (apply Hsub; done).
    iDestruct "Htlbor" as "[Htlbor_a | Hfin]".
    - iDestruct "Htlbor_a" as "[Hmach Hacked]".
      iMod (remote_ack γ tlb n i m Him Hall with "Hmach Hauth Hi Htlb Hacked") as "(Hmach' & Hauth' & Hacked')".
      iMod ("Hclose" with "[Hgo Hcnt Hauth' Hmach' Hacked']") as "_".
      { iNext. iExists (delete i m), (S k). rewrite Nat2Z.inj_succ. iFrame "Hgo Hcnt Hauth'".
        iSplitL "Hmach' Hacked'".
        - iLeft. iFrame "Hmach' Hacked'".
        - iPureIntro. split.
          + rewrite (size_dom_delete m i Him).
            assert (Hsz : 0 < size (dom m)) by
              (apply Nat.neq_0_lt_0; apply (proj2 (size_non_empty_iff (dom m))); set_solver).
            lia.
          + rewrite dom_delete_L. set_solver. }
      iModIntro. wp_pures. by iApply "HΦ".
    - iDestruct "Hfin" as "[_ %Hmempty]". exfalso. subst m. set_solver.
  Qed.

  Lemma cleared_tlbs_all_cores (n : nat) (m : gmap nat (exclR unitO)) (tlb : loc) :
    dom m = ∅ →
    ([∗ set] j ∈ (all_cores n ∖ dom m), (tlb +ₗ Z.of_nat j) ↦ encode_tlb None) -∗
    ([∗ set] j ∈ all_cores n, (tlb +ₗ Z.of_nat j) ↦ encode_tlb None).
  Proof.
    intros Hdom. rewrite (all_cores_clear n m Hdom). iIntros "$".
  Qed.

  (* -------- the leader's ack-counter wait: spin until cnt == n -------- *)

  Lemma wait_cnt_spec (γ γtok : gname) (tlb go cnt : loc) (n : nat) :
    {{{ inv N (sd_inv γ γtok tlb go cnt n) ∗ own γtok (Excl ()) }}}
      wait_cnt #cnt #n
    {{{ RET #(); machine_ctx γm (broadcast_post_machine root va mem n) ∗
                 [∗ set] j ∈ all_cores n, (tlb +ₗ Z.of_nat j) ↦ encode_tlb None }}}.
  Proof.
    iIntros (Φ) "[#HI Htok] HΦ".
    iLöb as "IH" forall (Φ).
    wp_rec. wp_pures.
    wp_bind (! #cnt)%E.
    iInv "HI" as (m k) "(>Hgo & >Hcnt & >Hauth & >Htlbor & >%Hpure)" "Hclose".
    wp_load.
    destruct (decide (k = n)) as [-> | Hne].
    - (* final iteration: k = n, so all cores have acked (m = ∅). Extract the
         cleared TLBs and the machine ([tls_of ∅] is all-[None], i.e.
         [broadcast_post_machine]), deposit the token (branch b), and return. *)
      iDestruct "Htlbor" as "[Htlbor_a | Hfin]".
      + iDestruct "Htlbor_a" as "[Hmach Hacked]".
        iMod (ghost_var_update (broadcast_post_machine root va mem n)
                                γm (reify_machine root va mem invalid_pte (tls_of m) n)
                with "Hmach") as "Hmach'".
        iMod ("Hclose" with "[Hgo Hcnt Hauth Htok]") as "_".
        { iNext. iExists m, n. iFrame "Hgo Hcnt Hauth". iSplitL.
          - iRight. iFrame "Htok". iPureIntro. exact (sd_pure_done n m Hpure).
          - iPureIntro. exact Hpure. }
        iModIntro. wp_pures.
        rewrite (bool_decide_true (LitV (LitInt (Z.of_nat n)) = LitV (LitInt (Z.of_nat n)))) //.
        wp_pures.
        pose proof (sd_pure_dom_empty n m Hpure) as Hdom.
        iDestruct (cleared_tlbs_all_cores n m tlb Hdom with "Hacked") as "Hacked'".
        iApply "HΦ".
        iModIntro.
        iFrame "Hmach' Hacked'".
      + (* branch (b): the token would be held both by the leader and the invariant. *)
        iDestruct "Hfin" as "[Htok' _]".
        iDestruct (own_valid_2 with "Htok Htok'") as %Hv.
        exfalso. exact (exclusive_l (Excl ()) (Excl ()) Hv).
    - (* loop: k ≠ n *)
      iMod ("Hclose" with "[Hgo Hcnt Hauth Htlbor]") as "_".
      { iNext. iExists m, k. iFrame "Hgo Hcnt Hauth Htlbor". iPureIntro. done. }
      iModIntro. wp_pures.
      assert (Hneq : LitV (LitInt (Z.of_nat k)) ≠ LitV (LitInt (Z.of_nat n))) by
        (intros H; apply Hne; apply Nat2Z.inj; congruence).
      rewrite (bool_decide_false (LitV (LitInt (Z.of_nat k)) = LitV (LitInt (Z.of_nat n))) Hneq).
      wp_pures. wp_apply ("IH" with "Htok").
      iIntros "Hacked". iApply ("HΦ" with "Hacked").
  Qed.

  (* -------- the forking loop: spawn remote j for j = i .. n-1 -------- *)

  Lemma all_cores_step (n i : nat) :
    i < n →
    all_cores n ∖ all_cores i = {[i]} ∪ (all_cores n ∖ all_cores (i + 1)).
  Proof.
    intros Hin. apply set_eq. intro x.
    setoid_rewrite elem_of_difference.
    setoid_rewrite elem_of_union.
    setoid_rewrite elem_of_singleton.
    setoid_rewrite elem_of_difference.
    setoid_rewrite elem_of_all_cores.
    intuition lia.
  Qed.

  Lemma fork_remotes_spec (γ γtok : gname) (tlb go cnt : loc) (i n : nat) :
    {{{ inv N (sd_inv γ γtok tlb go cnt n) ∗
        [∗ set] j ∈ (all_cores n ∖ all_cores i),
          own γ (◯ {[j := Excl ()]}) ∗ (tlb +ₗ Z.of_nat j) ↦ encode_tlb (Some leaf_entry) }}}
      fork_remotes #tlb #go #cnt #i #n
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[#HI Hrest] HΦ".
    iLöb as "IH" forall (i Φ).
    wp_rec. wp_pures.
    destruct (decide (i < n)) as [Hin | Hnot].
    - assert (HinZ : (Z.of_nat i < Z.of_nat n)%Z) by lia.
      rewrite (bool_decide_true ((Z.of_nat i < Z.of_nat n)%Z) HinZ).
      wp_pures.
      rewrite (all_cores_step n i Hin).
      rewrite big_sepS_union; last first.
      { intros x Hx. apply elem_of_singleton_1 in Hx; subst x.
        intros Hi. apply elem_of_difference in Hi as [Hn Hnotin].
        exfalso. apply Hnotin. apply elem_of_all_cores. lia. }
      rewrite big_sepS_singleton.
      iDestruct "Hrest" as "[Htok_i Hrest']".
      iDestruct "Htok_i" as "[Htok_i Htlbi]".
      wp_smart_apply (wp_fork with "[Htok_i Htlbi]").
      + iNext. iApply (remote_spec γ γtok tlb go cnt n i with "[$HI $Htok_i $Htlbi]").
        iNext. iIntros "_". done.
      + wp_pures.
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (i + 1))%Z by lia.
        wp_apply ("IH" with "Hrest'").
        iIntros "_". by iApply "HΦ".
    - assert (HnotZ : ¬ (Z.of_nat i < Z.of_nat n)%Z) by lia.
      rewrite (bool_decide_false ((Z.of_nat i < Z.of_nat n)%Z) HnotZ).
      wp_pures. by iApply "HΦ".
  Qed.

  (* -------- pure helpers for broadcast_spec -------- *)

  Lemma all_cores_0 : all_cores 0 = ∅.
  Proof. rewrite /all_cores. reflexivity. Qed.

  Lemma size_all_cores (n : nat) : size (all_cores n) = n.
  Proof.
    rewrite /all_cores size_list_to_set.
    - rewrite length_seq. lia.
    - apply NoDup_seq.
  Qed.

  Lemma loc_add_S (l : loc) (i : nat) : l +ₗ (S i) = (l +ₗ 1) +ₗ i.
  Proof.
    rewrite Loc.add_assoc Loc.eq_spec /= Nat2Z.inj_succ. lia.
  Qed.

  Lemma array_replicate_seq (l : loc) (n : nat) (v : val) :
    l ↦∗ replicate n v ⊣⊢ [∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v.
  Proof.
    revert l. induction n as [| n' IH]; intros l.
    - cbn [replicate seq]. rewrite array_nil big_sepL_nil. done.
    - cbn [replicate seq].
      rewrite array_cons big_sepL_cons Nat2Z.inj_0 Loc.add_0.
      rewrite (IH (l +ₗ 1)).
      rewrite -fmap_S_seq big_sepL_fmap.
      setoid_rewrite loc_add_S.
      done.
  Qed.

  Lemma big_sepL_seq_all_cores (Φ : nat → iProp Σ) (n : nat) :
    ([∗ list] i ∈ seq 0 n, Φ i)%I ⊣⊢ [∗ set] i ∈ all_cores n, Φ i.
  Proof.
    rewrite /all_cores -big_sepS_list_to_set; [done | apply NoDup_seq].
  Qed.

  (* Fuses the [Z.to_nat (Z.of_nat n)] normalization of the [AllocN] length with the
     list-to-set bridge, since Coq's [rewrite ... in H] cannot touch an Iris hypothesis. *)
  Lemma array_replicate_all_cores (l : loc) (n : nat) (v : val) :
    l ↦∗ replicate (Z.to_nat (Z.of_nat n)) v ⊣⊢
    [∗ set] i ∈ all_cores n, (l +ₗ Z.of_nat i) ↦ v.
  Proof.
    rewrite (array_replicate_seq l (Z.to_nat (Z.of_nat n)) v).
    rewrite Nat2Z.id.
    rewrite (big_sepL_seq_all_cores (λ i, (l +ₗ Z.of_nat i) ↦ v)%I n).
    reflexivity.
  Qed.

  (* -------- the leader: setup, fork, wait --------

     Reification invariant (HeapLang -> Machine). The machine ghost lives *inside*
     [sd_inv], derived from the pending map [m]:
       machine_ctx γm (reify_machine root va mem invalid_pte (tls_of m) n)
     so a core caches [leaf_entry] exactly while it is pending (j ∈ dom m) and has
     an empty TLB once it has acked. The leaf PTE is fixed invalid from the
     break-before-make write onward, matching the program's `pte <- invalid_pte`
     before the fork.

       - setup:     m = pending_map n, so [tls_of m = fun _ => Some leaf_entry] and
                    the machine is [reify_machine ... invalid_pte ...] (PTE already
                    invalid; every core stale).
       - remote ack: remote_ack advances the machine to [tls_of (delete i m)] in
                    lockstep with the auth-map update [m -> delete i m].
       - leader wait: at k = n, m = ∅, so the machine is [broadcast_post_machine].

     The machine-level conclusion is `broadcast_reifies_machine` (pure, above),
     which cites `invalidate_shootdown_empty_cores` to prove [Forall (translate =
     None /\ tlb_lookup = None)] on every core of `broadcast_post_machine`.

     Honesty note: each step uses [ghost_var_update], which is logically valid for
     any a -> b, so the *logic* does not force the machine to track [m]; the
     faithfulness is by construction of the proof (the ghost is only ever advanced
     to the canonical [tls_of]-reified value implied by the constrained auth-map
     update). Enforcing the coupling in the logic (per-cell ghost state with
     store-transfer) is a larger follow-up. *)

  Lemma broadcast_spec (n : nat) :
    {{{ ⌜0 < n⌝ ∗ machine_ctx γm (broadcast_pre_machine root va mem n) }}}
      broadcast #n
    {{{ RET #(); ∃ (γ γtok : gname) (pte tlb go cnt : loc),
        inv N (sd_inv γ γtok tlb go cnt n) ∗
        ([∗ set] j ∈ all_cores n, (tlb +ₗ Z.of_nat j) ↦ encode_tlb None) ∗
        pte ↦ encode_pte invalid_pte ∗
        machine_ctx γm (broadcast_post_machine root va mem n) }}}.
  Proof.
    iIntros (Φ) "[Hn Hm0] HΦ". iDestruct "Hn" as %Hn.
    wp_rec. wp_pures.
    wp_alloc pte as "Hpte".
    wp_alloc tlb as "Htlb"; first by lia.
    wp_alloc go as "Hgo".
    wp_alloc cnt as "Hcnt".
    (* break-before-make: the leaf PTE is written invalid before the fork. The
       machine ghost advances from the pre-machine to the invariant's machine
       (PTE invalid, every core still caching [leaf_entry] = [tls_of (pending_map n)]). *)
    wp_store. wp_store.
    iMod (ghost_var_update (reify_machine root va mem invalid_pte (tls_of (pending_map n)) n)
                            γm (broadcast_pre_machine root va mem n) with "Hm0") as "Hm1".
    iMod (own_alloc (● (pending_map n) ⋅ ◯ (pending_map n))) as (γ) "[Hauth Hfrag]";
      first by apply auth_both_valid_2; [apply pending_map_valid | reflexivity].
    iMod (own_alloc (Excl ())) as (γtok) "Htok"; first done.
    iMod (inv_alloc N _ (sd_inv γ γtok tlb go cnt n) with "[Hgo Hcnt Hauth Hm1]") as "#HI".
    { iNext. iExists (pending_map n), 0. iFrame "Hgo Hcnt Hauth".
      iSplit.
      - iLeft. iFrame "Hm1". rewrite dom_pending_map difference_diag_L. done.
      - iPureIntro. split.
        + rewrite dom_pending_map size_all_cores. lia.
        + rewrite dom_pending_map. set_solver. }
    iDestruct (pending_tokens_split γ n with "Hfrag") as "Htoks".
    iDestruct (array_replicate_all_cores tlb n (encode_tlb (Some leaf_entry))
                 with "Htlb") as "HtlbS".
    iDestruct (big_sepS_sep_2 (λ j, own γ (◯ {[j := Excl ()]}))
                    (λ j, (tlb +ₗ Z.of_nat j) ↦ encode_tlb (Some leaf_entry))%I (all_cores n)
               with "Htoks HtlbS") as "Hrest".
    iAssert (([∗ set] j ∈ (all_cores n ∖ all_cores 0),
                own γ (◯ {[j := Excl ()]}) ∗ (tlb +ₗ Z.of_nat j) ↦ encode_tlb (Some leaf_entry)))%I
      with "[Hrest]" as "Hrest0".
    { rewrite all_cores_0 difference_empty_L. done. }
    wp_apply (fork_remotes_spec γ γtok tlb go cnt 0 n with "[$HI $Hrest0]"); [iIntros "_"].
    wp_pures.
    wp_apply (wait_cnt_spec γ γtok tlb go cnt n with "[$HI $Htok]"); [iIntros "[Hmach Htlb_cleared]"].
    iApply "HΦ".
    iExists γ, γtok, pte, tlb, go, cnt. iFrame "Htlb_cleared Hpte Hmach". iFrame "#".
  Qed.

End proof.


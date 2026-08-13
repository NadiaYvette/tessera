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
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang.lib Require Import par.

Definition invalid_pte : Pte :=
  {| Pte_valid := false; Pte_read := true; Pte_write := true;
     Pte_exec := true; Pte_user := true; Pte_ppn := mword_of_int 0 |}.

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
  λ: "cnt" "n",
    (rec: "w" "x" := if: (!"cnt") = "n" then #() else "w" #()) #().

Definition remote : val :=
  λ: "tlb" "go" "cnt" "i",
    wait "go" ;;
    ("tlb" +ₗ "i") <- encode_tlb None ;;
    "cnt" <- !"cnt" + #1.

Definition fork_remotes : val :=
  λ: "tlb" "go" "cnt" "i" "n",
    (rec: "f" "j" :=
      if: "j" < "n"
      then (Fork (remote "tlb" "go" "cnt" "j") ;; "f" ("j" + #1))
      else #()) "i".

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
Definition sd_pure (n k : nat) (m : gmap nat (exclR unitO)) (b : bool) : Prop :=
  k + size (dom m) = n ∧ dom m ⊆ all_cores n ∧ (k = 0 ∨ b = true).

Class sdG Σ := SdG { sd_inG : inG Σ (authR (gmapUR nat (exclR unitO)));
                      sd_tokG : inG Σ (exclR unitO) }.
Local Existing Instances sd_inG sd_tokG.
Definition sdΣ : gFunctors := #[GFunctor (authR (gmapUR nat (exclR unitO))); GFunctor (exclR unitO)].
Global Instance subG_sdΣ {Σ} : subG sdΣ Σ → sdG Σ.
Proof. solve_inG. Qed.

(* ============================================================
   The concurrent proof.
   ============================================================ *)

Definition pending_map (n : nat) : gmap nat (exclR unitO) :=
  gset_to_gmap (Excl ()) (all_cores n).

Lemma elem_of_all_cores (n i : nat) : i ∈ all_cores n ↔ i < n.
Proof.
  rewrite /all_cores elem_of_list_to_set elem_of_seq. lia.
Qed.

Lemma size_dom_delete {A} `{Countable A} (m : gmap A (exclR unitO)) (i : A) :
  i ∈ dom m → size (dom (delete i m)) = size (dom m) - 1.
Proof.
  intros Hi. rewrite !size_dom. rewrite map_size_delete_Some.
  - lia.
  - apply elem_of_dom. done.
Qed.

Section proof.
  Context `{!heapGS Σ, !spawnG Σ, !sdG Σ}.
  Let N := nroot .@ "sd".

  Definition sd_inv (γ γtok : gname) (tlb go cnt : loc) (n : nat) : iProp Σ :=
    (∃ (b : bool) (m : gmap nat (exclR unitO)) (k : nat),
       go ↦ #b ∗
       cnt ↦ #k ∗
       own γ (● m) ∗
       (if b then ([∗ set] j ∈ (all_cores n ∖ dom m), (tlb +ₗ Z.of_nat j) ↦ encode_tlb None)
                  ∨ (own γtok (Excl ()) ∗ ⌜ m = ∅ ⌝)
        else True) ∗
       ⌜ sd_pure n k m b ⌝)%I.

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

  Lemma wait_spec (γ γtok : gname) (tlb go cnt : loc) (n : nat) :
    {{{ inv N (sd_inv γ γtok tlb go cnt n) }}}
      wait #go
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "#HI HΦ".
    iLöb as "IH" forall (Φ).
    wp_rec. wp_pures.
    wp_bind (! #go)%E.
    iInv "HI" as (b m k) "(>Hgo & >Hcnt & >Hauth & >Htlbor & >Hpure)" "Hclose".
    iDestruct "Hpure" as %Hpure.
    wp_load.
    destruct b.
    - iMod ("Hclose" with "[Hgo Hcnt Hauth Htlbor]") as "_".
      { iNext. iExists true, m, k. iFrame "Hgo Hcnt Hauth Htlbor". iPureIntro. done. }
      iModIntro. wp_pures. by iApply "HΦ".
    - iMod ("Hclose" with "[Hgo Hcnt Hauth Htlbor]") as "_".
      { iNext. iExists false, m, k. iFrame "Hgo Hcnt Hauth Htlbor". iPureIntro. done. }
      iModIntro. wp_pures. by iApply ("IH" with "HΦ").
  Qed.

End proof.


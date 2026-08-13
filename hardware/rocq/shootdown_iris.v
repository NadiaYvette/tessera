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

From iris.algebra Require Import auth gset.
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

Class sdG Σ := SdG { sd_inG : inG Σ (authR (gsetUR nat)) }.
Local Existing Instance sd_inG.
Definition sdΣ : gFunctors := #[GFunctor (authR (gsetUR nat))].
Global Instance subG_sdΣ {Σ} : subG sdΣ Σ → sdG Σ.
Proof. solve_inG. Qed.

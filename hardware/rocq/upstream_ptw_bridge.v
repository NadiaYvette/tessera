From Stdlib Require Import ZArith.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import machine_types.
Require Import machine.

Inductive PTW_Error_up := PTW_No_Access_up | PTW_Invalid_PTE_up | PTW_Misaligned_up.
Record PTW_Output_up := mk_PTW_Output_up { ptw_ppn_z : Z; ptw_level_z : Z }.

Fixpoint read_pte_z (mem : list (Z * mword 64)) (addr : Z) : option (mword 64) :=
  match mem with
  | nil => None
  | cons (a, v) rest => if Z.eqb a addr then Some v else read_pte_z rest addr
  end.

Definition is_invalid_z (pte : mword 64) : bool :=
  eq_vec (subrange_vec_dec pte 0 0) (mword_of_int 0).

Definition is_nonleaf_z (pte : mword 64) : bool :=
  eq_vec (subrange_vec_dec pte 3 3) (mword_of_int 0)
  && eq_vec (subrange_vec_dec pte 2 2) (mword_of_int 0)
  && eq_vec (subrange_vec_dec pte 1 1) (mword_of_int 0).

Definition ppn_of_z (pte : mword 64) : Z :=
  Z.shiftr (Z_of_N (mword_to_N pte)) 10 mod (2 ^ 44).

Definition vpn_i_z (vpn : mword 27) (level : nat) : Z :=
  match level with
  | 0%nat => Z.land (Z_of_N (mword_to_N vpn)) 511
  | 1%nat => Z.shiftr (Z_of_N (mword_to_N vpn)) 9 mod 512
  | 2%nat => Z.shiftr (Z_of_N (mword_to_N vpn)) 18 mod 512
  | _ => 0
  end.

Fixpoint pt_walk_up_z (mem : list (Z * mword 64))
  (vpn : mword 27) (base_ppn : Z) (level : nat) {struct level} :
  sum PTW_Output_up PTW_Error_up :=
  let addr := base_ppn * 4096 + vpn_i_z vpn level * 8 in
  match read_pte_z mem addr with
  | None => inr PTW_No_Access_up
  | Some pte =>
    if is_invalid_z pte then inr PTW_Invalid_PTE_up
    else if is_nonleaf_z pte then
      match level with
      | S level' => pt_walk_up_z mem vpn (ppn_of_z pte) level'
      | O => inr PTW_Invalid_PTE_up
      end
    else
      let ppn := ppn_of_z pte in
      match level with
      | O => inl (mk_PTW_Output_up ppn 0)
      | 1%nat =>
        if Z.gtb (ppn mod 512) 0 then inr PTW_Misaligned_up
        else inl (mk_PTW_Output_up ppn 1)
      | 2%nat =>
        if Z.gtb (ppn mod (2^18)) 0 then inr PTW_Misaligned_up
        else inl (mk_PTW_Output_up ppn 2)
      | S (S _) => inl (mk_PTW_Output_up ppn (Z.of_nat level))
      end
  end.

Definition nl_z (ppn_int : Z) : mword 64 := mword_of_int (ppn_int * 1024 + 1).
Definition leaf_z (ppn_int : Z) : mword 64 := mword_of_int (ppn_int * 1024 + 3).

Definition vpn0_z : mword 27 := mword_of_int 0.

(* Test read_pte_z finds the right address *)
Definition test_mem_z : list (Z * mword 64) :=
  (0, nl_z 4096) :: (16777216, nl_z 512) :: (2097152, leaf_z 768) :: nil.

Lemma test_read_0 : read_pte_z test_mem_z 0 = Some (nl_z 4096).
Proof. reflexivity. Qed.

Lemma test_read_16777216 : read_pte_z test_mem_z 16777216 = Some (nl_z 512).
Proof. reflexivity. Qed.

Lemma test_ppn : ppn_of_z (nl_z 4096) = 4096.
Proof. reflexivity. Qed.

Lemma test_vpn_i_0 : vpn_i_z vpn0_z 0 = 0.
Proof. reflexivity. Qed.

Lemma test_vpn_i_1 : vpn_i_z vpn0_z 1 = 0.
Proof. reflexivity. Qed.

(* Full walk: level 2, base=0, vpn=0 *)
Lemma test_full : pt_walk_up_z test_mem_z vpn0_z 0 2 = inl (mk_PTW_Output_up 768 0).
Proof. reflexivity. Qed.

Lemma test_level1 :
  pt_walk_up_z test_mem_z vpn0_z 0 1 = inr PTW_Invalid_PTE_up.
Proof. reflexivity. Qed.

Lemma test_level0 :
  pt_walk_up_z test_mem_z vpn0_z 0 0 = inr PTW_Invalid_PTE_up.
Proof. reflexivity. Qed.

Lemma test_empty :
  pt_walk_up_z nil vpn0_z 0 2 = inr PTW_No_Access_up.
Proof. reflexivity. Qed.

Lemma test_only_l2 :
  pt_walk_up_z ((0, nl_z 4096) :: nil) vpn0_z 0 2 = inr PTW_No_Access_up.
Proof. reflexivity. Qed.

Lemma test_l0_leaf :
  pt_walk_up_z ((0, leaf_z 100) :: nil) vpn0_z 0 0 = inl (mk_PTW_Output_up 100 0).
Proof. reflexivity. Qed.

(* Tessera — G1 upstream-gen-bridge: generated pte_is_invalid
   agrees with transcribed upstream_pte_is_invalid from machine.sail,
   for all Sv39 PTEs (A=D=U=0, PBMT=RSW=reserved=0).
   32 exhaustive test vectors for (V,R,W,X,N) in bool^5.
   8 exhaustive test vectors for (R,W,X) in bool^3 (non-leaf).
   All theorems axiom-free. *)

From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import machine_types.
Require Import machine.
Require Import upstream_vmem_pte_types.
Require Import upstream_vmem_pte.

(* ---- pte_is_invalid: 32 test vectors (V,R,W,X,N) in bool^5 ---- *)

Lemma vec_v0r0w0x0n0 :
  pte_is_invalid (mword_of_int 0 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r0w0x0n1 :
  pte_is_invalid (mword_of_int 0 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r0w0x1n0 :
  pte_is_invalid (mword_of_int 8 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r0w0x1n1 :
  pte_is_invalid (mword_of_int 8 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r0w1x0n0 :
  pte_is_invalid (mword_of_int 4 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r0w1x0n1 :
  pte_is_invalid (mword_of_int 4 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r0w1x1n0 :
  pte_is_invalid (mword_of_int 12 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r0w1x1n1 :
  pte_is_invalid (mword_of_int 12 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r1w0x0n0 :
  pte_is_invalid (mword_of_int 2 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r1w0x0n1 :
  pte_is_invalid (mword_of_int 2 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r1w0x1n0 :
  pte_is_invalid (mword_of_int 10 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r1w0x1n1 :
  pte_is_invalid (mword_of_int 10 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r1w1x0n0 :
  pte_is_invalid (mword_of_int 6 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r1w1x0n1 :
  pte_is_invalid (mword_of_int 6 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r1w1x1n0 :
  pte_is_invalid (mword_of_int 14 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v0r1w1x1n1 :
  pte_is_invalid (mword_of_int 14 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r0w0x0n0 :
  pte_is_invalid (mword_of_int 1 : mword 8)
               (mword_of_int 0 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r0w0x0n1 :
  pte_is_invalid (mword_of_int 1 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r0w0x1n0 :
  pte_is_invalid (mword_of_int 9 : mword 8)
               (mword_of_int 0 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r0w0x1n1 :
  pte_is_invalid (mword_of_int 9 : mword 8)
               (mword_of_int 512 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r0w1x0n0 :
  pte_is_invalid (mword_of_int 5 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r0w1x0n1 :
  pte_is_invalid (mword_of_int 5 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r0w1x1n0 :
  pte_is_invalid (mword_of_int 13 : mword 8)
               (mword_of_int 0 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r0w1x1n1 :
  pte_is_invalid (mword_of_int 13 : mword 8)
               (mword_of_int 512 : mword 10) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r1w0x0n0 :
  pte_is_invalid (mword_of_int 3 : mword 8)
               (mword_of_int 0 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r1w0x0n1 :
  pte_is_invalid (mword_of_int 3 : mword 8)
               (mword_of_int 512 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r1w0x1n0 :
  pte_is_invalid (mword_of_int 11 : mword 8)
               (mword_of_int 0 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r1w0x1n1 :
  pte_is_invalid (mword_of_int 11 : mword 8)
               (mword_of_int 512 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r1w1x0n0 :
  pte_is_invalid (mword_of_int 7 : mword 8)
               (mword_of_int 0 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r1w1x0n1 :
  pte_is_invalid (mword_of_int 7 : mword 8)
               (mword_of_int 512 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r1w1x1n0 :
  pte_is_invalid (mword_of_int 15 : mword 8)
               (mword_of_int 0 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma vec_v1r1w1x1n1 :
  pte_is_invalid (mword_of_int 15 : mword 8)
               (mword_of_int 512 : mword 10) = false.
Proof. vm_compute. reflexivity. Qed.

(* ---- pte_is_non_leaf: 8 test vectors (R,W,X) in bool^3 ---- *)

Lemma nl_r0w0x0 :
  pte_is_non_leaf (mword_of_int 1 : mword 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_r0w0x1 :
  pte_is_non_leaf (mword_of_int 9 : mword 8) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_r0w1x0 :
  pte_is_non_leaf (mword_of_int 5 : mword 8) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_r0w1x1 :
  pte_is_non_leaf (mword_of_int 13 : mword 8) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_r1w0x0 :
  pte_is_non_leaf (mword_of_int 3 : mword 8) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_r1w0x1 :
  pte_is_non_leaf (mword_of_int 11 : mword 8) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_r1w1x0 :
  pte_is_non_leaf (mword_of_int 7 : mword 8) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma nl_r1w1x1 :
  pte_is_non_leaf (mword_of_int 15 : mword 8) = false.
Proof. vm_compute. reflexivity. Qed.
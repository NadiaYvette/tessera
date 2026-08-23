(* Tessera — Custom RISC-V MMU extension: Inverted Page Table
   Hash consistency proofs and test vectors.

   Bitvector constants: vaddr = 64-bit, sp_vpn = 56-bit.
   Uses SailStdpp ('b"...") notation with exact-width strings.
*)

From stdpp Require Import base countable pretty.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import riscv_inverted_pt_types.
Require Import riscv_inverted_pt.
Import ListNotations.

Open Scope Z_scope.

(* eq_vec_refl helper *)
Lemma eq_vec_refl {n} (v : mword n) : eq_vec v v = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.

(* ============================================================
   Generic lemmas
   ============================================================ *)

Lemma phipt_hash_deterministic_eqvec :
  forall (sp1 sp2 : mword 56) (part1 part2 : mword 2),
    eq_vec sp1 sp2 = true ->
    eq_vec part1 part2 = true ->
    eq_vec (phipt_hash sp1 part1) (phipt_hash sp2 part2) = true.
Proof.
  intros sp1 sp2 part1 part2 Hsp Hpart.
  apply eq_vec_true_iff in Hsp.
  apply eq_vec_true_iff in Hpart.
  rewrite Hsp, Hpart. apply eq_vec_refl.
Qed.

Lemma sp_vpn_hash_consistency :
  forall (va1 va2 : mword 64) (sz : mword 6) (part : mword 2),
    eq_vec (sp_vpn_of va1 sz) (sp_vpn_of va2 sz) = true ->
    eq_vec (phipt_hash (sp_vpn_of va1 sz) part)
           (phipt_hash (sp_vpn_of va2 sz) part) = true.
Proof.
  intros va1 va2 sz part Hsame.
  apply eq_vec_true_iff in Hsame.
  rewrite Hsame. apply eq_vec_refl.
Qed.

Lemma partition_deterministic :
  forall (sz1 sz2 : mword 6),
    eq_vec sz1 sz2 = true ->
    eq_vec (partition_of sz1) (partition_of sz2) = true.
Proof.
  intros sz1 sz2 Hsz.
  apply eq_vec_true_iff in Hsz.
  rewrite Hsz. apply eq_vec_refl.
Qed.

Lemma covers_implies_same_hash :
  forall (e : PhiTlbEntry) (va : mword 64),
    phi_covers e va = true ->
    forall (part : mword 2),
      eq_vec (phipt_hash (sp_vpn_of va (PhiTlbEntry_size e)) part)
             (phipt_hash (PhiTlbEntry_sp_vpn e) part) = true.
Proof.
  intros e va Hcover part.
  unfold phi_covers in Hcover.
  apply eq_vec_true_iff in Hcover.
  rewrite Hcover. apply eq_vec_refl.
Qed.

(* ============================================================
   Test vectors — all bitstrings exactly match their width
   ============================================================ *)

(* 64-bit VAs *)
Definition va_4k_a : mword 64 :=
  'b"0000000000000000000000000000000000000000000000000001000000000000".  (* 0x1000 *)
Definition va_4k_b : mword 64 :=
  'b"0000000000000000000000000000000000000000000000000001000000001000".  (* 0x1008 *)
Definition va_64k_a : mword 64 :=
  'b"0000000000000000000000000000000000000000000000010000000000000000".  (* 0x10000 *)
Definition va_64k_b : mword 64 :=
  'b"0000000000000000000000000000000000000000000000011111111111111111".  (* 0x1FFFF *)
Definition va_4k_x : mword 64 :=
  'b"0000000000000000000000000000000000000000000000001010000000000000".  (* 0xA000 *)
Definition va_4k_y : mword 64 :=
  'b"0000000000000000000000000000000000000000000000001010111111111111".  (* 0xAFFF *)
Definition va_page2 : mword 64 :=
  'b"0000000000000000000000000000000000000000000000000010000000000000".  (* 0x2000 *)
Definition va_128k : mword 64 :=
  'b"0000000000000000000000000000000000000000000000100000000000000000".  (* 0x20000 *)

(* 6-bit sizes *)
Definition sz_4k  : mword 6 := 'b"001100".   (* 12 *)
Definition sz_13  : mword 6 := 'b"001101".   (* 13 *)
Definition sz_16  : mword 6 := 'b"010000".   (* 16 *)
Definition sz_64k : mword 6 := 'b"010000".   (* 16 (same) *)

(* 2-bit partition *)
Definition part_0 : mword 2 := 'b"00".
Definition part_1 : mword 2 := 'b"01".

(* Tests: 4KB hash consistency *)
Lemma test_hash_4k :
  eq_vec (phipt_hash (sp_vpn_of va_4k_a sz_4k) part_0)
         (phipt_hash (sp_vpn_of va_4k_b sz_4k) part_0) = true.
Proof. vm_compute. reflexivity. Qed.

(* Tests: 64KB hash consistency *)
Lemma test_hash_64k :
  eq_vec (phipt_hash (sp_vpn_of va_64k_a sz_64k) part_0)
         (phipt_hash (sp_vpn_of va_64k_b sz_64k) part_0) = true.
Proof. vm_compute. reflexivity. Qed.

(* Tests: partition differs for sz=12 vs sz=13 *)
Lemma test_partition_differs :
  eq_vec (partition_of sz_4k) (partition_of sz_13) = false.
Proof. vm_compute. reflexivity. Qed.

(* Tests: partition same for sz=12 vs sz=16 (differ by 4) *)
Lemma test_partition_same_4 :
  eq_vec (partition_of sz_4k) (partition_of sz_16) = true.
Proof. vm_compute. reflexivity. Qed.

(* Tests: sp_vpn agrees for VAs in same 4KB block *)
Lemma test_sp_vpn_4k_agree :
  eq_vec (sp_vpn_of va_4k_x sz_4k) (sp_vpn_of va_4k_y sz_4k) = true.
Proof. vm_compute. reflexivity. Qed.

(* Tests: sp_vpn differs across 4KB boundary *)
Lemma test_sp_vpn_4k_differ :
  eq_vec (sp_vpn_of va_4k_a sz_4k) (sp_vpn_of va_page2 sz_4k) = false.
Proof. vm_compute. reflexivity. Qed.

(* Tests: sp_vpn agrees for VAs in same 64KB block *)
Lemma test_sp_vpn_64k_agree :
  eq_vec (sp_vpn_of va_64k_a sz_64k) (sp_vpn_of va_64k_b sz_64k) = true.
Proof. vm_compute. reflexivity. Qed.

(* Tests: sp_vpn differs across 64KB boundary *)
Lemma test_sp_vpn_64k_differ :
  eq_vec (sp_vpn_of va_64k_a sz_64k) (sp_vpn_of va_128k sz_64k) = false.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   Summary: 4 generic lemmas + 8 test vectors = 12 total
   All axiom-free. Uses Sail-generated model directly.
   ============================================================ *)
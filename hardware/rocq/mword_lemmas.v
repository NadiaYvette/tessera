(* Tessera — `mword`/`uint` distribution lemmas.

   SailStdpp's `mword`/`uint` are defined over the `MachineWord` module, which
   the SailStdpp interface leaves *abstract* (`word_to_N` is a parameter with
   only a range axiom).  But the concrete instance `MachineWord` is
   transparent in this switch (`MachineWord.word = bv`,
   `MachineWord.word_to_N = λ n w, Z.to_N (bv_unsigned w)`), so every
   composite op unfolds to stdpp's `bv_*` and the stdpp `bv_*_unsigned`
   lemmas discharge the arithmetic.  These lemmas unblock the *general*
   StageOA identity in `aarch64_sail_oracle.v` (previously pinned only by
   concrete `vm_compute` vectors).

   Nothing here relies on the interface's range axioms.  The width-`Z` <->
   width-`N` plumbing of `subrange_vec_dec`/`concat_vec` is handled by
   SailStdpp's own `autocast_refl` / `word_to_N_cast_idx` preservation lemmas
   (`uint_autocast` / `uint_to_word_idx` below), not by `vm_compute` (which
   does not scale: it normalises the `Z_to_bv` well-formedness obligations).
*)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.MachineWord.
Require Import SailStdpp.Values.
From stdpp Require Import bitvector.definitions.

Open Scope Z_scope.

(* ============================================================
   `uint` is `bv_unsigned` (the N round-trip is the identity on the
   always-non-negative `bv_unsigned`).
   ============================================================ *)

Lemma uint_bv_unsigned {a} (x : mword a) : uint x = bv_unsigned x.
Proof.
  unfold uint, MachineWord.word_to_N, get_word.
  apply Z2N.id. apply bv_unsigned_in_range.
Qed.

Lemma uint_nonneg {a} (x : mword a) : 0 <= uint x.
Proof. rewrite uint_bv_unsigned. apply bv_unsigned_in_range. Qed.

(* ============================================================
   `bv_wrap` / `bv_modulus` at a Z-indexed width.
   ============================================================ *)

Lemma bv_wrap_mword {a} (z : Z) : 0 <= a -> bv_wrap (Z.to_N a) z = z mod 2^a.
Proof.
  intro Ha. unfold bv_wrap, bv_modulus.
  rewrite Z2N.id by lia. reflexivity.
Qed.

Lemma bv_modulus_mword {a} : 0 <= a -> bv_modulus (Z.to_N a) = 2^a.
Proof.
  intro Ha. unfold bv_modulus. rewrite Z2N.id by lia. reflexivity.
Qed.

(* ============================================================
   Width-cast preservation: `uint` ignores the `autocast` / `to_word_idx`
   width-`Z` <-> width-`N` plumbing.
   ============================================================ *)

Lemma uint_autocast {m n} (x : mword m) (H : m = n) :
  uint (@autocast mword m n _ x) = uint x.
Proof.
  subst n.
  rewrite (@autocast_refl mword m _ x).
  reflexivity.
Qed.

Lemma uint_to_word_idx {n} (w : MachineWord.word n) :
  uint (to_word_idx w) = Z.of_N (MachineWord.word_to_N w).
Proof.
  unfold to_word_idx, to_word, uint, get_word.
  rewrite word_to_N_cast_idx.
  reflexivity.
Qed.

(* ============================================================
   `shiftr` / `shiftl`: shift-amount plumbing through `N_to_word`.
   ============================================================ *)

(* The shift amount, as seen by the bv-level shift, is `n mod 2^a`. *)
Lemma bv_unsigned_N_to_word_mword {a} (n : Z) :
  0 <= a -> 0 <= n ->
  bv_unsigned (MachineWord.N_to_word (Z.to_N a) (MachineWord.Z_idx n)) = n mod 2^a.
Proof.
  intros Ha Hn.
  unfold MachineWord.N_to_word, MachineWord.Z_idx.
  rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_mword by lia.
  rewrite Z2N.id by lia.
  reflexivity.
Qed.

Lemma uint_shiftr {a} (v : mword a) (n : Z) :
  0 <= a -> 0 <= n < 2^a ->
  uint (shiftr v n) = uint v / 2^n.
Proof.
  intros Ha Hn.
  rewrite !uint_bv_unsigned.
  unfold shiftr, with_word, MachineWord.logical_shift_right.
  rewrite bv_shiftr_unsigned.
  rewrite bv_unsigned_N_to_word_mword by lia.
  assert (Hsmall : n mod 2^a = n) by (apply Z.mod_small; exact Hn).
  rewrite Hsmall.
  rewrite Z.shiftr_div_pow2 by lia.
  reflexivity.
Qed.

Lemma uint_shiftl {a} (v : mword a) (n : Z) :
  0 <= a -> 0 <= n < 2^a ->
  uint (shiftl v n) = (uint v * 2^n) mod 2^a.
Proof.
  intros Ha Hn.
  rewrite !uint_bv_unsigned.
  unfold shiftl, with_word, MachineWord.logical_shift_left.
  rewrite bv_shiftl_unsigned.
  rewrite bv_unsigned_N_to_word_mword by lia.
  assert (Hsmall : n mod 2^a = n) by (apply Z.mod_small; exact Hn).
  rewrite Hsmall.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite bv_wrap_mword by lia.
  reflexivity.
Qed.

(* ============================================================
   `or_vec` and `zero_extend`.
   ============================================================ *)

Lemma uint_or_vec {a} (x y : mword a) :
  uint (or_vec x y) = Z.lor (uint x) (uint y).
Proof.
  rewrite !uint_bv_unsigned.
  unfold or_vec, word_binop, with_word', with_word, MachineWord.or.
  rewrite bv_or_unsigned.
  reflexivity.
Qed.

Lemma uint_zero_extend {a n} (v : mword a) :
  0 <= a -> a <= n ->
  uint (zero_extend v n) = uint v.
Proof.
  intros Ha Han.
  rewrite !uint_bv_unsigned.
  unfold zero_extend, extz_vec, to_word, MachineWord.zero_extend.
  rewrite bv_zero_extend_unsigned'.
  rewrite bv_wrap_mword by lia.
  apply Z.mod_small.
  pose proof (bv_unsigned_in_range (Z.to_N a) v) as Hr.
  rewrite bv_modulus_mword in Hr by lia.
  destruct Hr as [Hr0 Hrlt].
  split.
  - exact Hr0.
  - apply (Z.lt_le_trans _ (2^a) (2^n)).
    + exact Hrlt.
    + apply Z.pow_le_mono_r; lia.
Qed.

(* ============================================================
   Z-arithmetic helpers for the StageOA identity: "take the low k bits"
   and "bitwise OR of a shifted value and a low value is their sum".
   ============================================================ *)

Lemma shift_mod_div (x k n : Z) :
  0 <= k -> k <= n ->
  ((x * 2^k) mod 2^n) / 2^k = x mod 2^(n-k).
Proof.
  intros Hk Hkn.
  assert (Hpow : 2^n = 2^(n-k) * 2^k).
  { replace (2^n) with (2^((n-k)+k)).
    - apply Z.pow_add_r; lia.
    - f_equal. lia. }
  rewrite Hpow.
  rewrite Z.mul_mod_distr_r by (apply Z.pow_nonzero; lia).
  rewrite Z.div_mul by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.

Lemma Z_land_mul_pow2_0 (a m b : Z) :
  0 <= a -> 0 <= m -> 0 <= b < 2^m ->
  Z.land (a * 2^m) b = 0.
Proof.
  intros Ha Hm Hb.
  destruct Hb as [Hb0 Hb2m].
  apply Z.bits_inj. intro n.
  rewrite Z.land_spec, Z.testbit_0_l.
  destruct (Z.lt_ge_cases n 0) as [Hneg | Hn0].
  - rewrite Z.testbit_neg_r by lia.
    reflexivity.
  - destruct (Z.lt_ge_cases n m) as [Hlt | Hge].
    + rewrite <- Z.shiftl_mul_pow2 by lia.
      rewrite Z.shiftl_spec by lia.
      rewrite Z.testbit_neg_r by lia.
      rewrite Bool.andb_false_l. reflexivity.
    + destruct (Z.eq_dec b 0) as [Hb0' | Hbgt].
      * subst b. rewrite Z.testbit_0_l.
        rewrite Bool.andb_false_r. reflexivity.
      * assert (Hbn : Z.testbit b n = false).
        { apply Z.bits_above_log2; [lia |].
          apply (Z.lt_le_trans _ m n); [| exact Hge].
          apply Z.log2_lt_pow2; [lia | exact Hb2m]. }
        rewrite Hbn.
        rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma Z_lor_add_pow2 (a m b : Z) :
  0 <= a -> 0 <= m -> 0 <= b < 2^m ->
  Z.lor (a * 2^m) b = a * 2^m + b.
Proof.
  intros Ha Hm Hb.
  rewrite <- (Z.add_lor_land (a * 2^m) b).
  rewrite (Z_land_mul_pow2_0 a m b Ha Hm Hb).
  lia.
Qed.

(* ============================================================
   `subrange_vec_dec` (bit slice) — the `55..0` case used by `aa_pa`.
   Concrete bounds reduce the `autocast`/`cast_idx` width plumbing via the
   cast-preservation lemmas above (no `vm_compute`).
   ============================================================ *)

Lemma uint_subrange_vec_dec_55_0 (v : mword 64) :
  uint (subrange_vec_dec v 55 0) = uint v mod 2^56.
Proof.
  unfold subrange_vec_dec.
  rewrite uint_autocast by reflexivity.
  rewrite uint_to_word_idx.
  unfold MachineWord.slice, MachineWord.word_to_N.
  rewrite Z2N.id by (apply bv_unsigned_in_range).
  rewrite bv_extract_unsigned.
  rewrite Z.shiftr_0_r.
  rewrite bv_wrap_mword by lia.
  rewrite uint_bv_unsigned.
  reflexivity.
Qed.

(* Tessera — differential oracle: the AArch64 variant (`aarch64_tlb.sail`)
   agrees with the vendored `sail-arm` model's page-size machinery.

   `hardware/src/sail_arm_tlb.sail` extracts `ContiguousSize`/`TGxGranuleBits`/
   `TranslationSize` *verbatim* (modulo totality and the `TGx -> SaTGx` rename)
   from `third_party/sail-arm/arm-v9.4-a/src/v8_base.sail`.  That extraction is
   generated into `sail_arm_tlb.v` and imported here *qualified* (so its
   `vaddr`/`paddr`/`register` scaffolding does not collide with
   `aarch64_tlb_types`), and the two models are bridged by `bit_of_bool`
   (`bool` <-> `bits(1)`) and `sa_of_tgx` (`TGx` <-> `SaTGx`).

   What is proved here, all axiom-free:

     1. **General (all inputs)** — `sa_tgx_granule_bits_conforms`,
        `sa_translation_size_conforms`, `sa_contiguous_size_conforms`: the three
        Z-valued size functions agree on *every* d128/tgx/level, i.e. the whole
        `{4KB,16KB,64KB} x level x CONT` size spectrum is transcribed exactly.
     2. **`sa_ia_msb_conforms`** — the `ia_msb = translation_size +
        (contig ? contiguous_size : 0)` boundary agrees for every `AaEntry`.
     3. **StageOA address part** — proved *generally* by `aa_stage_oa_spec`
        (below): for every entry and address with `0 <= aa_ia_msb <= 55`,
        `uint (aa_pa e va) = (uint oabase * 2^12 / 2^m) * 2^m + uint va mod 2^m`,
        i.e. `baseaddress.address[55..m] @ va[m-1..0]`.  The SailStdpp
        `mword`/`uint` distribution lemmas in `mword_lemmas.v`
        (`uint_or_vec`/`uint_shiftl`/`uint_shiftr`/`uint_zero_extend`/
        `uint_subrange_vec_dec_55_0`, plus the cast-preservation
        `uint_autocast`/`uint_to_word_idx`) discharge the shift/or plumbing,
        closing the gap the earlier `vm_compute` vectors only pinned concretely.

   Source lines (v8_base.sail): `ContiguousSize` l. 19962, `TGxGranuleBits`
   l. 20008, `TranslationSize` l. 20026, `StageOA` l. 20038.
*)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import aarch64_tlb_types.
Require Import aarch64_tlb.
Require Import aarch64_tlb_proofs.   (* reuses aa_2m / aa_va_* fixtures *)
Require Import mword_lemmas.         (* uint-distribution + StageOA arithmetic *)
From stdpp Require Import bitvector.definitions.
(* The vendored sail-arm extraction, imported qualified so its `vaddr`/`paddr`/
   `bit`/`bits`/register scaffolding does not collide with aarch64_tlb_types. *)
Require sail_arm_tlb_types.
Require sail_arm_tlb.
Import ListNotations.

Open Scope Z_scope.

(* ============================================================
   Bridges between the two transcriptions' representations.
   ============================================================ *)

Definition bit_of_bool (b : bool) : mword 1 := if b then ('b"1") else ('b"0").

Definition sa_of_tgx (tgx : TGx) : sail_arm_tlb_types.SaTGx :=
  match tgx with
  | TGx_4KB  => sail_arm_tlb_types.SaTGx_4KB
  | TGx_16KB => sail_arm_tlb_types.SaTGx_16KB
  | TGx_64KB => sail_arm_tlb_types.SaTGx_64KB
  end.

(* ============================================================
   General equivalence: the size spectrum is transcribed exactly.
   ============================================================ *)

Lemma sa_tgx_granule_bits_conforms (tgx : TGx) :
  sail_arm_tlb.sa_tgx_granule_bits (sa_of_tgx tgx) = tgx_granule_bits tgx.
Proof.
  destruct tgx; reflexivity.
Qed.

Lemma sa_translation_size_conforms (d128 : bool) (tgx : TGx) (level : Z) :
  sail_arm_tlb.sa_translation_size (bit_of_bool d128) (sa_of_tgx tgx) level
  = translation_size d128 tgx level.
Proof.
  destruct d128; destruct tgx; vm_compute; reflexivity.
Qed.

Lemma sa_contiguous_size_conforms (d128 : bool) (tgx : TGx) (level : Z) :
  sail_arm_tlb.sa_contiguous_size (bit_of_bool d128) (sa_of_tgx tgx) level
  = contiguous_size d128 tgx level.
Proof.
  destruct d128; destruct tgx; vm_compute; reflexivity.
Qed.

(* ============================================================
   The StageOA ia_msb boundary (v8_base.sail l. 20045-20047):
     ia_msb = TranslationSize + (contiguous ? ContiguousSize : 0).
   ============================================================ *)

Definition sa_ia_msb (d128 : bool) (tgx : TGx) (level : Z) (contig : bool) : Z :=
  let tsize := sail_arm_tlb.sa_translation_size (bit_of_bool d128) (sa_of_tgx tgx) level in
  let csize := if contig then sail_arm_tlb.sa_contiguous_size (bit_of_bool d128) (sa_of_tgx tgx) level else 0 in
  tsize + csize.

Lemma sa_ia_msb_conforms (e : AaEntry) :
  sa_ia_msb (AaEntry_d128 e) (AaEntry_tgx e) (AaEntry_level e) (AaEntry_contig e)
  = aa_ia_msb e.
Proof.
  unfold sa_ia_msb, aa_ia_msb.
  rewrite sa_translation_size_conforms.
  destruct (AaEntry_contig e).
  - rewrite sa_contiguous_size_conforms. reflexivity.
  - reflexivity.
Qed.

(* ============================================================
   StageOA address part (v8_base.sail l. 20051):
     oa.address = baseaddress.address[55 .. ia_msb] @ ia[ia_msb - 1 .. 0]
   transcribed via SailStdpp's `subrange_vec_dec`/`concat_vec`, pinned against
   the shift-based `aa_pa` by vm_compute (the general bit-vector identity is
   blocked on the abstract MachineWord interface).
   ============================================================ *)

(* The StageOA address concat is written per-vector with ia_msb *concrete*,
   since `concat_vec`/`subrange_vec_dec` are size-dependent and a free ia_msb
   cannot be reduced to 56 by the typechecker (the same reason sail-arm itself
   needs `assert(constraint(0 <= ia_msb <= 55))`).  The ia_msb boundary is
   already proven general in `sa_ia_msb_conforms`; these vectors pin the final
   bit-slicing (`baseaddr[55..ia_msb] @ ia[ia_msb-1..0]`) against the
   shift-based `aa_pa`.) *)

(* sail-arm's `baseaddress.address : bits(56)` is the *full* OA base address
   (oabase << 12), so the StageOA concat extracts from these 56-bit values. *)
Definition sa_oa_base_2m : mword 56 := mword_of_int 0x200000.  (* = aa_oa_2m << 12 *)
Definition sa_oa_base_4k : mword 56 := mword_of_int 0x1000.    (* = aa_oa1   << 12 *)
Definition sa_oa_base_ct : mword 56 := mword_of_int 0x10000.   (* = aa_oa_ct  << 12 *)

(* 2 MB block: ia_msb = sa_ia_msb false TGx_4KB 2 false = 21. *)
Lemma diff_stage_oa_2m :
  uint (concat_vec (subrange_vec_dec sa_oa_base_2m 55 21)
                   (subrange_vec_dec aa_va_1234 20 0))
  = uint (aa_pa aa_2m aa_va_1234).
Proof. vm_compute. reflexivity. Qed.

(* 4 KB page: ia_msb = sa_ia_msb false TGx_4KB 3 false = 12. *)
Lemma diff_stage_oa_4k :
  uint (concat_vec (subrange_vec_dec sa_oa_base_4k 55 12)
                   (subrange_vec_dec aa_va_1234 11 0))
  = uint (aa_pa (aa_4k aa_vatag1) aa_va_1234).
Proof. vm_compute. reflexivity. Qed.

(* 64 KB contpte: ia_msb = sa_ia_msb false TGx_4KB 3 true = 12 + 4 = 16. *)
Lemma diff_stage_oa_contig :
  uint (concat_vec (subrange_vec_dec sa_oa_base_ct 55 16)
                   (subrange_vec_dec aa_va_1234 15 0))
  = uint (aa_pa aa_4k_contig aa_va_1234).
Proof. vm_compute. reflexivity. Qed.

(* A 2 MB block does not cover a VA in the adjacent 2 MB region (cross-check
   that the StageOA boundary matches the coverage boundary). *)
Lemma diff_stage_oa_2m_next :
  uint (concat_vec (subrange_vec_dec sa_oa_base_2m 55 21)
                   (subrange_vec_dec aa_va_200000 20 0))
  = uint (aa_pa aa_2m aa_va_200000).
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   The *general* StageOA identity (v8_base.sail l. 20038-20051):

     oa.address = baseaddress.address[55 .. ia_msb] @ ia[ia_msb - 1 .. 0]

   as a Z-level statement about the shift-based `aa_pa`:

     uint (aa_pa e va)
     = (uint oabase * 2^12 / 2^m) * 2^m + uint va mod 2^m,

   where `baseaddress.address = oabase << 12` is the 56-bit OA base.  This is
   what the per-vector `diff_stage_oa_*` pins above only at concrete `ia_msb`;
   the lemma below holds for *every* entry/address with the architecturally
   valid `0 <= ia_msb <= 55`, discharging the `or_vec`/`shiftl`/`shiftr`/
   `zero_extend`/`subrange_vec_dec` plumbing via `mword_lemmas.v`.
   ============================================================ *)

Lemma aa_stage_oa_spec (e : AaEntry) (va : mword 64) :
  0 <= aa_ia_msb e <= 55 ->
  uint (aa_pa e va)
  = (uint (AaEntry_oabase e) * 2^12 / 2^(aa_ia_msb e)) * 2^(aa_ia_msb e)
    + uint va mod 2^(aa_ia_msb e).
Proof.
  intro Hm_range.
  unfold aa_pa.
  set (m := aa_ia_msb e) in *.
  destruct Hm_range as [Hm0 Hm55].
  assert (Hm_le_64 : m <= 64) by lia.
  assert (Hm_lt_256 : m < 2^56) by (apply (Z.le_lt_trans m 55 (2^56)); [exact Hm55 | vm_compute; constructor]).
  assert (Hm_lt_264 : m < 2^64) by (apply (Z.le_lt_trans m 55 (2^64)); [exact Hm55 | vm_compute; constructor]).
  assert (H64m_ge0 : 0 <= 64 - m) by lia.
  assert (H64m_lt264 : 64 - m < 2^64) by (apply (Z.le_lt_trans (64-m) 64 (2^64)); [lia | vm_compute; constructor]).
  assert (H12_lt : 0 <= 12 < 2^56) by (split; [lia | vm_compute; constructor]).

  assert (Hoabase_lt : uint (AaEntry_oabase e) < 2^44)
    by (rewrite uint_bv_unsigned; apply bv_unsigned_in_range).
  assert (Hoabase_12_lt : uint (AaEntry_oabase e) * 2^12 < 2^56).
  { apply (Z.lt_le_trans _ (2^44 * 2^12) (2^56)).
    - apply Z.mul_lt_mono_pos_r.
      + apply Z.pow_pos_nonneg; lia.
      + exact Hoabase_lt.
    - rewrite <- Z.pow_add_r by lia. lia. }

  (* H_oa_hi *)
  assert (H_oa_hi : uint (shiftr (shiftl (zero_extend (AaEntry_oabase e) 56) 12) m)
                    = uint (AaEntry_oabase e) * 2^12 / 2^m).
  { rewrite uint_shiftr; [| lia | split; [exact Hm0 | exact Hm_lt_256]].
    rewrite uint_shiftl; [| lia | exact H12_lt].
    rewrite uint_zero_extend; [| lia | lia].
    rewrite Z.mod_small by (split; [apply Z.mul_nonneg_nonneg; [apply uint_nonneg | apply Z.pow_nonneg; lia] | exact Hoabase_12_lt]).
    reflexivity. }

  (* quotient facts *)
  assert (Hq_nonneg : 0 <= (uint (AaEntry_oabase e) * 2^12) / 2^m)
    by (apply Z.div_pos; [apply Z.mul_nonneg_nonneg; [apply uint_nonneg | apply Z.pow_nonneg; lia] | apply Z.pow_pos_nonneg; lia]).
  assert (Hq_le : (uint (AaEntry_oabase e) * 2^12) / 2^m * 2^m <= uint (AaEntry_oabase e) * 2^12).
  { rewrite (Z.mul_comm ((uint (AaEntry_oabase e) * 2^12) / 2^m) (2^m)).
    apply Z.mul_div_le. apply Z.pow_pos_nonneg; lia. }
  assert (Hquot_lt : (uint (AaEntry_oabase e) * 2^12) / 2^m * 2^m < 2^56)
    by (apply (Z.le_lt_trans _ (uint (AaEntry_oabase e) * 2^12) (2^56)); [exact Hq_le | exact Hoabase_12_lt]).

  (* H_oa_shift *)
  assert (H_oa_shift : uint (shiftl (shiftr (shiftl (zero_extend (AaEntry_oabase e) 56) 12) m) m)
                       = (uint (AaEntry_oabase e) * 2^12 / 2^m) * 2^m).
  { rewrite uint_shiftl; [| lia | split; [exact Hm0 | exact Hm_lt_256]].
    rewrite H_oa_hi.
    rewrite Z.mod_small by (split; [apply Z.mul_nonneg_nonneg; [exact Hq_nonneg | apply Z.pow_nonneg; lia] | exact Hquot_lt]).
    reflexivity. }

  (* H_off *)
  assert (H_off : uint (shiftr (shiftl va (64-m)) (64-m)) = uint va mod 2^m).
  { rewrite uint_shiftr; [| lia | split; [exact H64m_ge0 | exact H64m_lt264]].
    rewrite uint_shiftl; [| lia | split; [exact H64m_ge0 | exact H64m_lt264]].
    rewrite shift_mod_div by lia.
    replace (64 - (64 - m)) with m by lia.
    reflexivity. }

  (* off mod 2^56 is small *)
  assert (Hoff_lt : uint va mod 2^m < 2^56)
    by (apply (Z.lt_le_trans _ (2^m) (2^56)); [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).

  (* H_off_sub *)
  assert (H_off_sub : uint (zero_extend (subrange_vec_dec (shiftr (shiftl va (64-m)) (64-m)) 55 0) 56)
                      = uint va mod 2^m).
  { rewrite uint_zero_extend; [| lia | lia].
    rewrite uint_subrange_vec_dec_55_0.
    rewrite H_off.
    rewrite Z.mod_small by (split; [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia | exact Hoff_lt]).
    reflexivity. }

  rewrite uint_or_vec.
  rewrite H_oa_shift, H_off_sub.
  apply Z_lor_add_pow2.
  - exact Hq_nonneg.
  - exact Hm0.
  - apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia.
Qed.

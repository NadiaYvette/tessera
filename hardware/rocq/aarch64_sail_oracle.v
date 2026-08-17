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
     3. **StageOA address part** — pinned by `vm_compute` vectors, since the
        general bit-vector identity (`subrange`/`concat` vs the shift-based
        `aa_pa`) is blocked on SailStdpp's abstract `MachineWord` interface not
        exposing word-distribution lemmas (see loongarch-software-refill.md).

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

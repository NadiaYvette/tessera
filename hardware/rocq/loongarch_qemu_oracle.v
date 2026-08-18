(* Tessera — G1 differential test for the third MMU variant: the
   Sail-generated LoongArch software-refill TLB (`loongarch_tlb.v`, from
   `hardware/src/loongarch_tlb.sail`) vs the QEMU oracle.

   The oracle is a faithful transcription of QEMU's loongarch64 TCG on the
   `nadia.chambers/page-grain-001` branch (the only oracle — there is no
   upstream Sail model for LoongArch):

   - `target/loongarch/tcg/tlb_helper.c` `loongarch_tlb_search_cb` (the
     `compare_shift = ps + 1 - 13` / `vpn = va[47:0] >> (ps+1)` pair match),
     `loongarch_map_tlb_entry` (`n = (addr >> ps) & 1` odd/even).
   - `target/loongarch/cpu_helper.c` `loongarch_check_pte`
     (`tlb_ppn = pfn & ~((1 << (ps-12)) - 1)`; `physical = (tlb_ppn << 12) |
     (addr & ((1 << ps) - 1))`).

   The model and the oracle use *different* expressions for the same
   semantics, so the agreement below genuinely exercises the transcription:

   | aspect | model (`loongarch_tlb.sail`) | QEMU oracle |
   |---|---|---|
   | match | `(va[47:0] >> (ps+1)) == (vppn << 13 >> (ps+1))` (48-bit) | `(va[47:0] >> (ps+1)) == zero_extend(vppn >> (ps+1-13), 48)` |
   | odd/even | `(va >> ps)[0] == 1` | same (`n = (addr >> ps) & 1`) |
   | PA | `(pfn >> (ps-12)) << ps \| va[ps-1:0]` | `((pfn & ~((1<<(ps-12))-1)) << 12) \| (va & ((1<<ps)-1))` |

   The match agreement is proved **generally** (`la_covers_conforms`:
   every entry/address, for `12 <= ps <= 47`) via the shift identity
   `shiftr (shiftl x 13) (ps+1) = zero_extend (shiftr x (ps+1-13)) 48`,
   unblocked by `mword_lemmas.v`'s concrete `MachineWord` instance.  The PA
   agreement is likewise proved **generally** (`la_pa_conforms`, every
   entry/address, for `12 <= ps <= 48`): the core identity is
   `pfn & (2^36 - 2^(ps-12)) = (pfn >> (ps-12)) << (ps-12)` (the QEMU
   `tlb_ppn = pfn & ~((1 << (ps-12)) - 1)` clear, `Z_land_clear_low` in
   `mword_lemmas.v`).  The `vm_compute` diff vectors below remain as
   executable smoke tests of both directions.
*)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.MachineWord.
Require Import mword_lemmas.
From stdpp.bitvector Require Import definitions tactics.
Require Import loongarch_tlb_types.
Require Import loongarch_tlb.
Require Import loongarch_tlb_proofs. (* la_entry_4k/16k, la_vppn*, la_va_* *)
Import ListNotations.

Open Scope Z_scope.

(* ============================================================
   The oracle: loongarch_tlb_search_cb / loongarch_check_pte.
   ============================================================ *)

(* `compare_shift = tlb_ps + 1 - R_TLB_MISC_VPPN_SHIFT` (VPPN_SHIFT = 13);
   the pair match compares `va[47:0] >> (ps+1)` with `vppn >> (ps+1-13)`
   (zero-extended to 48 bits to align with the 48-bit VA slice). *)
Definition qemu_la_match (e : LaEntry) (va : mword 64) : bool :=
  let ps := e.(LaEntry_ps) in
  eq_vec (shiftr (subrange_vec_dec va 47 0) (Z.add ps 1))
         (zero_extend (shiftr e.(LaEntry_vppn) (Z.add (Z.sub ps 13) 1)) 48).

(* `loongarch_map_tlb_entry`: n = (addr >> ps) & 1 selects the odd half. *)
Definition qemu_la_odd (e : LaEntry) (va : mword 64) : bool :=
  eq_vec (subrange_vec_dec (shiftr va e.(LaEntry_ps)) 0 0) ('b"1").

Definition qemu_la_pfn (e : LaEntry) (va : mword 64) : mword 36 :=
  if qemu_la_odd e va then e.(LaEntry_pfn1) else e.(LaEntry_pfn0).

(* `loongarch_check_pte`: `tlb_ppn = pfn & ~((1 << (ps-12)) - 1)` (clear the
   software bits between bit 12 and ps), `physical = (tlb_ppn << 12) |
   (addr & ((1 << ps) - 1))`. *)
Definition qemu_la_pa (e : LaEntry) (va : mword 64) : mword 48 :=
  let ps := e.(LaEntry_ps) in
  let pfn := qemu_la_pfn e va in
  let swmask : mword 36 := mword_of_int (Z.pow 2 (Z.sub ps 12) - 1) in
  let tlb_ppn := and_vec pfn (not_vec swmask) in
  or_vec (shiftl (zero_extend tlb_ppn 48) 12)
         (zero_extend (subrange_vec_dec (shiftr (shiftl va (Z.sub 64 ps)) (Z.sub 64 ps)) 47 0) 48).

(* ============================================================
   Diff vectors: the model and the QEMU transcription agree.
   ============================================================ *)

(* Match: the 4 KiB entry covers both halves of its pair; agree on each. *)
Lemma diff_la_match_4k_even :
  la_covers (la_entry_4k la_vppn1) la_va_4k_even =
  qemu_la_match (la_entry_4k la_vppn1) la_va_4k_even.
Proof. vm_compute. reflexivity. Qed.
Lemma diff_la_match_4k_odd :
  la_covers (la_entry_4k la_vppn1) la_va_4k_odd =
  qemu_la_match (la_entry_4k la_vppn1) la_va_4k_odd.
Proof. vm_compute. reflexivity. Qed.
Lemma diff_la_match_4k_next :
  la_covers (la_entry_4k la_vppn1) la_va_4k_next = false
  /\ qemu_la_match (la_entry_4k la_vppn1) la_va_4k_next = false.
Proof. vm_compute. tauto. Qed.
(* Match: 16 KiB pair (ps = 14), both halves + next-pair rejection. *)
Lemma diff_la_match_16k_even :
  la_covers (la_entry_16k la_vppn4) la_va_16k_even =
  qemu_la_match (la_entry_16k la_vppn4) la_va_16k_even.
Proof. vm_compute. reflexivity. Qed.
Lemma diff_la_match_16k_odd :
  la_covers (la_entry_16k la_vppn4) la_va_16k_odd =
  qemu_la_match (la_entry_16k la_vppn4) la_va_16k_odd.
Proof. vm_compute. reflexivity. Qed.
Lemma diff_la_match_16k_next :
  la_covers (la_entry_16k la_vppn4) la_va_16k_next = false
  /\ qemu_la_match (la_entry_16k la_vppn4) la_va_16k_next = false.
Proof. vm_compute. tauto. Qed.

(* PA: `((pfn & ~mask) << 12) | (va & mask)` agrees with `la_pa` on both
   halves of the 4 KiB and 16 KiB pairs. *)
Lemma diff_la_pa_4k_even :
  uint (la_pa (la_entry_4k la_vppn1) la_va_4k_even) =
  uint (qemu_la_pa (la_entry_4k la_vppn1) la_va_4k_even).
Proof. vm_compute. reflexivity. Qed.
Lemma diff_la_pa_4k_odd :
  uint (la_pa (la_entry_4k la_vppn1) la_va_4k_odd) =
  uint (qemu_la_pa (la_entry_4k la_vppn1) la_va_4k_odd).
Proof. vm_compute. reflexivity. Qed.
Lemma diff_la_pa_16k_even :
  uint (la_pa (la_entry_16k la_vppn4) la_va_16k_even) =
  uint (qemu_la_pa (la_entry_16k la_vppn4) la_va_16k_even).
Proof. vm_compute. reflexivity. Qed.
Lemma diff_la_pa_16k_odd :
  uint (la_pa (la_entry_16k la_vppn4) la_va_16k_odd) =
  uint (qemu_la_pa (la_entry_16k la_vppn4) la_va_16k_odd).
Proof. vm_compute. reflexivity. Qed.

(* The odd/even selection agrees: va[ps] picks pfn1 on the odd halves. *)
Lemma diff_la_odd_even :
  qemu_la_odd (la_entry_4k la_vppn1) la_va_4k_even = false
  /\ qemu_la_odd (la_entry_4k la_vppn1) la_va_4k_odd = true.
Proof. vm_compute. tauto. Qed.

(* ============================================================
   General conformance (not just vm_compute pins): the model and the
   QEMU oracle agree for *every* entry/address, via the shift identity
   `shiftr (shiftl x 13) (ps+1) = zero_extend (shiftr x (ps+1-13)) 48`,
   unblocked by mword_lemmas.v's concrete MachineWord instance.
   ============================================================ *)

(* The core match identity: the model places vppn at VA bits [13:47] then
   shifts right by ps+1; the oracle shifts vppn right by ps+1-13 and
   zero-extends to 48.  They agree as 48-bit words whenever ps is a valid
   page shift (12 <= ps <= 47): vppn < 2^35, so vppn << 13 < 2^48 (no
   overflow), and dividing by 2^(ps+1) cancels the 2^13. *)
Lemma la_match_shift_conforms (vppn : mword 35) (ps : Z) :
  12 <= ps -> ps <= 47 ->
  shiftr (shiftl (zero_extend vppn 48) 13) (Z.add ps 1) =
  zero_extend (shiftr vppn (Z.add (Z.sub ps 13) 1)) 48.
Proof.
  intros Hps0 Hps1.
  apply bv_eq.
  rewrite <- !uint_bv_unsigned.
  rewrite uint_shiftr; [| lia | split; lia].
  rewrite uint_shiftl; [| lia | split; lia].
  rewrite uint_zero_extend by lia.
  rewrite uint_zero_extend by lia.
  rewrite uint_shiftr; [| lia | split; lia].
  assert (Hvppn_lt : uint vppn < 2^35).
  { rewrite uint_bv_unsigned.
    pose proof (bv_unsigned_in_range (Z.to_N 35) vppn) as Hr.
    rewrite (bv_modulus_mword (a := 35)) in Hr by lia.
    destruct Hr as [_ Hlt]. exact Hlt. }
  assert (Hpow : 2^35 * 2^13 = 2^48).
  { rewrite <- Z.pow_add_r by lia. reflexivity. }
  assert (Hmul_lt : uint vppn * 2^13 < 2^48).
  { rewrite <- Hpow.
    apply (Zmult_lt_compat_r (uint vppn) (2^35) (2^13));
      [apply Z.pow_pos_nonneg; lia | exact Hvppn_lt]. }
  assert (Hmod : (uint vppn * 2^13) mod 2^48 = uint vppn * 2^13).
  { apply Z.mod_small. split.
    - apply Z.mul_nonneg_nonneg; [apply uint_nonneg | apply Z.pow_nonneg; lia].
    - exact Hmul_lt. }
  rewrite Hmod.
  replace (Z.add (Z.sub ps 13) 1) with (ps - 12) by lia.
  replace (Z.add ps 1) with (Z.add (ps - 12) 13) by lia.
  rewrite Z.pow_add_r by lia.
  apply Z.div_mul_cancel_r; apply Z.pow_nonzero; lia.
Qed.

(* General match conformance: the model's pair match and the oracle's
   `loongarch_tlb_search_cb` transcription agree for every entry/address. *)
Lemma la_covers_conforms (e : LaEntry) (va : mword 64) :
  12 <= e.(LaEntry_ps) <= 47 ->
  la_covers e va = qemu_la_match e va.
Proof.
  intros Hps. destruct Hps as [Hps0 Hps1].
  unfold la_covers, qemu_la_match.
  f_equal.
  apply la_match_shift_conforms; assumption.
Qed.

(* The high-part PA conformance, isolated: the model's `(pfn >> (ps-12)) << ps`
   agrees with the oracle's `((pfn & ~(2^(ps-12)-1)) << 12)` as 48-bit words.
   The core identity is `pfn & (2^36 - 2^(ps-12)) = (pfn >> (ps-12)) << (ps-12)`
   (`Z_land_clear_low` in mword_lemmas.v), i.e. clearing the software bits
   between bit 12 and ps equals shifting right then left. *)
Lemma la_pa_hi_conforms (pfn : mword 36) (ps : Z) :
  12 <= ps <= 48 ->
  uint (shiftl (zero_extend (shiftr pfn (ps-12)) 48) ps) =
  uint (shiftl (zero_extend (and_vec pfn (not_vec (mword_of_int (len := 36) (2^(ps-12)-1)))) 48) 12).
Proof.
  intros Hps. destruct Hps as [Hps0 Hps1].
  (* LHS: (uint (shiftr pfn (ps-12)) * 2^ps) mod 2^48 *)
  rewrite uint_shiftl; [| lia | split; lia].
  rewrite uint_zero_extend by lia.
  rewrite uint_shiftr; [| lia | split; lia].
  (* RHS: (uint (and_vec pfn (not_vec swmask)) * 2^12) mod 2^48 *)
  rewrite uint_shiftl; [| lia | split; lia].
  rewrite uint_zero_extend by lia.
  rewrite uint_and_vec.
  rewrite uint_not_vec by lia.
  rewrite (uint_swmask ps) by lia.
  replace (2^36 - 1 - (2^(ps-12) - 1)) with (2^36 - 2^(ps-12)) by lia.
  assert (Hu : 0 <= uint pfn < 2^36).
  { rewrite uint_bv_unsigned.
    pose proof (bv_unsigned_in_range (Z.to_N 36) pfn) as Hr.
    rewrite (bv_modulus_mword (a := 36)) in Hr by lia.
    cbn [MachineWord.Z_idx].
    lia. }
  assert (Hk0 : 0 <= ps - 12) by lia.
  assert (Hk36 : ps - 12 <= 36) by lia.
  rewrite (Z_land_clear_low (uint pfn) (ps - 12) Hk0 Hk36 Hu).
  rewrite <- Z.mul_assoc.
  replace (2^(ps-12) * 2^12) with (2^ps) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  reflexivity.
Qed.

(* General PA conformance: the model's `la_pa` and the oracle's
   `loongarch_check_pte` transcription agree for every entry/address.
   The two `or_vec` low parts are identical (`va[ps-1:0]`), so `f_equal`
   reduces this to `la_pa_hi_conforms` on the high part. *)
Lemma la_pa_conforms (e : LaEntry) (va : mword 64) :
  12 <= e.(LaEntry_ps) <= 48 ->
  uint (la_pa e va) = uint (qemu_la_pa e va).
Proof.
  intros Hps.
  unfold la_pa, qemu_la_pa, qemu_la_pfn, qemu_la_odd.
  rewrite !uint_or_vec.
  f_equal.
  exact (la_pa_hi_conforms (if eq_vec (subrange_vec_dec (shiftr va e.(LaEntry_ps)) 0 0) ('b"1")
                           then e.(LaEntry_pfn1) else e.(LaEntry_pfn0)) e.(LaEntry_ps) Hps).
Qed.

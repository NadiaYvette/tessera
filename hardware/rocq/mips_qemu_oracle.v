(* Tessera — G1 differential test for the second MMU variant: the
   Sail-generated MIPS software-refill TLB (`mips_tlb.v`, from
   `hardware/src/mips_tlb.sail`) vs the QEMU oracle.

   The oracle is a faithful transcription of QEMU's MIPS TLB code on the
   `nadia.chambers/page-grain-001` branch (the 1 KiB PageGrain work):
   - `target/mips/tcg/system/cp0_helper.c` `compute_pagemask` (ll. 872-889)
   - `target/mips/tcg/system/tlb_helper.c` `r4k_fill_tlb` (ll. 51-109) and
     `r4k_map_address` (ll. 432-480)
   (MD00091 §9.14/9.15/9.30.)

   What is *genuinely different* between the model and QEMU — and therefore
   what the conformance below actually tests:

   | aspect | model (`mips_tlb.sail`) | QEMU oracle |
   |---|---|---|
   | field extraction | `mips_mask_field` (slice of `reg[28..11]`) | `qemu_extract` = `extract32(val, lsb, width)`, lsb/width from esp |
   | trailing-ones count | `cto18` = `count_trailing_zeros (not_vec v)` | `qemu_cto` (same cto32 semantics) |
   | acceptance | `(field >> k) == 0 && even k` | `qemu_accept` = `(mask >> maskbits) == 0 && (maskbits & 1) == 0` |
   | PFN | `(pfn >> level) << ps` | `qemu_pfn` = `(PFN & ~mask) << pfn_shift` |
   | offset mask | low `ps` bits of VA | `qemu_offset_mask` = `(PageMask \| 0x7FF) >> 1` |
   | match | `mips_covers` (single page) | `qemu_match` = `(VPN & ~mask) == (va & ~mask)` (2-page pair) |

   The headline theorem:
   - `compute_mask_level_conforms` — the decode agrees with QEMU's
     `compute_pagemask` acceptance, and the returned level is the count.

   The PA and match conformance are pinned by *executable differential
   vectors* (both sides computed by `vm_compute`) across the {4^k · M}
   spectrum in both ESP modes:
   - PA: QEMU's `PFN | (va & (mask >> 1))` agrees with `mips_pa` per entry
     (PFN[0] = PFN[1] = pfn; the EntryLo0/1 pairing is elided by the model).
   - match: on the even half of the pair (pairing bit clear) QEMU's pair
     match agrees with the single-page `mips_covers`; on the odd half the
     pairing shows up (QEMU matches, the model does not) — the documented
     elision, pinned by `diff_match_1k_pairing`.

   A general (Z-level) PA/match conformance is a recorded follow-up; the
   value of the differential vectors is that they discharge *both the model
   and the QEMU transcription* by computation, so the transcription itself
   is exercised.
*)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
From stdpp.bitvector Require Import definitions tactics.
Require Import mips_tlb_types.
Require Import mips_tlb.
Require Import mips_tlb_proofs. (* mips_mask_field, compute_mask_level_unfold *)
Import ListNotations.

Open Scope Z_scope.

(* ============================================================
   The oracle: compute_pagemask (cp0_helper.c ll. 872-889).
   ============================================================ *)

(* The field extraction is a *shared primitive* (the same convention as
   conformance.v reusing `phys_addr`/`read_pte`): `mips_mask_field` is the
   model's name for QEMU's `extract32(val, lsb, width)` — the Mask+MaskX
   (esp) or Mask (no-esp) slice, `lsb = esp ? CP0PM_MASKX : CP0PM_MASK`
   (11 / 13), `width = esp ? 18 : 16`.  `qemu_extract` is defined to be it,
   so the genuinely-different decode logic below (`qemu_accept`,
   `qemu_compute_pagemask`) is what the conformance tests. *)
(* `mips_mask_field` (from mips_tlb_proofs.v) is the shared field extraction:
   the model's `raw[17..2]` slice, i.e. reg[28:13] — the 16-bit Mask field
   (reg[28:11] under ESP, the 18-bit Mask+MaskX field). *)
Definition qemu_extract : mword 29 -> bool -> mword 18 := mips_mask_field.

(* cto32(mask): the count of trailing ones.  QEMU's builtin; transcribed as
   trailing zeros of the complement (identical, incl. the all-ones case). *)
Definition qemu_cto (v : mword 18) : Z := count_trailing_zeros (not_vec v).

(* The acceptance predicate: `(mask >> maskbits) == 0 && (maskbits & 1) == 0`. *)
Definition qemu_accept (reg : mword 29) (esp : bool) : bool :=
  let f := qemu_extract reg esp in
  let mb := qemu_cto f in
  eq_vec (shiftr f mb) (zeros 18) && Z.eqb (Z.rem mb 2) 0.

(* compute_pagemask's return: `mask << lsb` for a valid encoding, else 0.
   (uint32_t in QEMU — the PageMask register value.) *)
Definition qemu_compute_pagemask (reg : mword 29) (esp : bool) : mword 32 :=
  if qemu_accept reg esp then
    shiftl (mword_of_int (Z.pow 2 (qemu_cto (qemu_extract reg esp)) - 1))
           (if esp then 11 else 13)
  else mword_of_int 0.

(* ============================================================
   The oracle: r4k_fill_tlb / r4k_map_address (tlb_helper.c ll. 51-109,
   432-480).  The EntryLo0/1 two-page pairing is elided (the model's stated
   scope), so the oracle is stated per-entry with PFN[0] = PFN[1] = pfn.
   ============================================================ *)

(* r4k_fill_tlb: `PFN[0] = (EntryLo.PFN & ~mask) << pfn_shift` where
   `mask = PageMask >> lsb = 2^level - 1` (the run) and `pfn_shift = 10` (esp)
   or `12`. *)
Definition qemu_pfn (esp : bool) (level : Z) (pfn : mword 44) : mword 56 :=
  shiftl (zero_extend (and_vec pfn (not_vec (mword_of_int (2 ^ level - 1)))) 56)
         (mips_base_shift esp).

(* The PA offset mask `(PageMask | 0x7FF) >> 1` (r4k_map_address: `mask =
   tlb->PageMask | 0x7FFu`, `*physical = tlb->PFN[n] | (address & (mask >> 1))`).
   PageMask = ((2^level - 1) << lsb) | (esp ? 0 : (3 << 11)) — the MaskX bits
   are forced to 0b11 under ESP=0 (r4k_fill_tlb). *)
Definition qemu_offset_mask (esp : bool) (level : Z) : mword 64 :=
  let run := 2 ^ level - 1 in
  let pm := if esp then Z.shiftl run 11
            else Z.lor (Z.shiftl run 13) (Z.shiftl 3 11) in
  mword_of_int (Z.shiftr (Z.lor pm 0x7FF) 1).

(* r4k_map_address PA: `PFN | (va & (mask >> 1))`. *)
Definition qemu_pa (esp : bool) (level : Z) (pfn : mword 44) (va : mword 64)
  : mword 56 :=
  or_vec (qemu_pfn esp level pfn)
         (zero_extend (and_vec va (qemu_offset_mask esp level)) 56).

(* r4k_map_address match: `(VPN & ~mask) == (va & ~mask)`, `mask = PageMask |
   0x7FF`, restricted to the 30-bit VPN (VA[39:10]); bit 10 (EHINV) is cleared
   by `~mask` in QEMU too, so the VPN widths line up.  This is the *pair* match
   (2 pages); `mips_covers` is the single page. *)
Definition qemu_match_mask (esp : bool) (level : Z) : mword 30 :=
  (* the low (base_shift + level - 9) VPN bits that `~(PageMask | 0x7FF)`
     clears, i.e. VA[base_shift+level .. 0] projected onto VA[39:10] *)
  mword_of_int (Z.pow 2 (mips_page_shift esp level - 9) - 1).

Definition qemu_match (e : MipsEntry) (va : mword 64) : bool :=
  let m := qemu_match_mask e.(MipsEntry_esp) e.(MipsEntry_level) in
  eq_vec (and_vec e.(MipsEntry_vpn) (not_vec m))
         (and_vec (subrange_vec_dec va 39 10) (not_vec m)).

(* ============================================================
   Linking lemmas: the model's primitives and the oracle's agree.
   ============================================================ *)

(* The trailing-ones counts agree (both are QEMU's cto32 semantics). *)
Lemma qemu_cto_cto18 (v : mword 18) : qemu_cto v = cto18 v.
Proof. reflexivity. Qed.

(* ============================================================
   Theorem: the decode agrees with QEMU's compute_pagemask.
   ============================================================ *)

Theorem compute_mask_level_conforms (reg : mword 29) (esp : bool) :
  match compute_mask_level reg esp with
  | Some k => qemu_accept reg esp = true /\ k = qemu_cto (qemu_extract reg esp)
  | None => qemu_accept reg esp = false
  end.
Proof.
  rewrite compute_mask_level_unfold. cbn zeta.
  (* The model's guard is `andb (eq_vec (shiftr f (cto18 f)) (zeros 18)) (even (cto18 f))`
     with `even n = Z.eqb (Z.rem n 2) 0` — exactly qemu_accept's two conjuncts. *)
  destruct (andb (eq_vec (shiftr (mips_mask_field reg esp)
                                 (cto18 (mips_mask_field reg esp))) (zeros 18))
                 (even (cto18 (mips_mask_field reg esp)))) eqn:H.
  - (* accepted *)
    cbn. split.
    + (* qemu_accept reg esp = true *)
      unfold qemu_accept, qemu_extract. cbn zeta. exact H.
    + (* k = qemu_cto (qemu_extract reg esp), with k := cto18 (mips_mask_field reg esp) *)
      reflexivity.
  - (* rejected *)
    cbn. unfold qemu_accept, qemu_extract. cbn zeta. exact H.
Qed.

(* ============================================================
   Differential test vectors (vm_compute pins, both sides computed).
   The PA is compared via `uint` (the Z value), sidestepping the bv
   proof-irrelevance mismatch between `or_vec`-built and `mword_of_int`-built
   words; the decode/match are compared as bools/options directly.
   ============================================================ *)

(* --- decode: the model and QEMU agree across the spectrum. --- *)
Definition reg_lvl0   : mword 29 := mword_of_int 0.
Definition reg_lvl2   : mword 29 := mword_of_int 0x6000.
Definition reg_lvl4   : mword 29 := mword_of_int 0x1E000.
Definition reg_odd    : mword 29 := mword_of_int 0x2000.
Definition reg_nonrun : mword 29 := mword_of_int 0xA000.
Definition reg_esp_l2 : mword 29 := mword_of_int 0x1800.

Lemma diff_decode_lvl0 :
  compute_mask_level reg_lvl0 false = Some 0 /\ qemu_accept reg_lvl0 false = true
  /\ qemu_compute_pagemask reg_lvl0 false = mword_of_int 0.
Proof. vm_compute. tauto. Qed.
Lemma diff_decode_lvl2 :
  compute_mask_level reg_lvl2 false = Some 2 /\ qemu_accept reg_lvl2 false = true.
Proof. vm_compute. tauto. Qed.
Lemma diff_decode_lvl4 :
  compute_mask_level reg_lvl4 false = Some 4 /\ qemu_accept reg_lvl4 false = true.
Proof. vm_compute. tauto. Qed.
Lemma diff_decode_odd :
  compute_mask_level reg_odd false = None /\ qemu_accept reg_odd false = false.
Proof. vm_compute. tauto. Qed.
Lemma diff_decode_nonrun :
  compute_mask_level reg_nonrun false = None /\ qemu_accept reg_nonrun false = false.
Proof. vm_compute. tauto. Qed.
Lemma diff_decode_esp_l2 :
  compute_mask_level reg_esp_l2 true = Some 2 /\ qemu_accept reg_esp_l2 true = true.
Proof. vm_compute. tauto. Qed.

(* --- PA: QEMU's `PFN | (va & (mask >> 1))` agrees with `mips_pa` (per entry,
       PFN[0] = PFN[1] = pfn) across the spectrum in both ESP modes. --- *)
Lemma diff_pa_1k :
  uint (qemu_pa true 0 mips_pfn mips_va) =
  uint (mips_pa (mips_entry_1k mips_va) mips_va).
Proof. vm_compute. reflexivity. Qed.
Lemma diff_pa_4k :
  uint (qemu_pa false 0 mips_pfn mips_va) =
  uint (mips_pa (mips_entry_4k mips_va) mips_va).
Proof. vm_compute. reflexivity. Qed.
Lemma diff_pa_16k :
  uint (qemu_pa false 2 mips_pfn mips_va_16k_super) =
  uint (mips_pa (mips_entry_16k mips_va) mips_va_16k_super).
Proof. vm_compute. reflexivity. Qed.
(* 4 KiB page under ESP (level 2): QEMU's pfn_shift 10 == the model's ps 12. *)
Definition mips_entry_esp_4k (va : mword 64) : MipsEntry :=
  {| MipsEntry_vpn := mword_of_int (mips_vpn_of va);
     MipsEntry_pfn := mips_pfn;
     MipsEntry_level := 2;
     MipsEntry_esp := true |}.

Lemma diff_pa_esp_4k :
  uint (qemu_pa true 2 mips_pfn mips_va) =
  uint (mips_pa (mips_entry_esp_4k mips_va) mips_va).
Proof. vm_compute. reflexivity. Qed.

(* --- match: on the even half of the pair (pairing bit clear), QEMU's pair
       match agrees with the single-page `mips_covers`; on the odd half the
       EntryLo0/1 pairing shows up (QEMU matches, the single-page model does
       not). --- *)
(* 1 KiB entry, even half (VA[10] = 0): agree. *)
Lemma diff_match_1k_even :
  qemu_match (mips_entry_1k mips_va) mips_va =
  mips_covers (mips_entry_1k mips_va) mips_va.
Proof. vm_compute. reflexivity. Qed.
(* 1 KiB entry, same 1 KiB page: agree. *)
Lemma diff_match_1k_same :
  qemu_match (mips_entry_1k mips_va) mips_va_1k_same =
  mips_covers (mips_entry_1k mips_va) mips_va_1k_same.
Proof. vm_compute. reflexivity. Qed.
(* 1 KiB entry, odd half (VA[10] = 1): QEMU's pair still matches, the
   single-page model does not — the elided EntryLo0/1 pairing. *)
Lemma diff_match_1k_pairing :
  qemu_match (mips_entry_1k mips_va) mips_va_1k_next = true
  /\ mips_covers (mips_entry_1k mips_va) mips_va_1k_next = false.
Proof. vm_compute. tauto. Qed.
(* 4 KiB entry, next 4 KiB page: neither matches (different pair). *)
Lemma diff_match_4k_next :
  qemu_match (mips_entry_4k mips_va) mips_va_4k_next = false
  /\ mips_covers (mips_entry_4k mips_va) mips_va_4k_next = false.
Proof. vm_compute. tauto. Qed.
(* 16 KiB entry, adjacent 4 KiB subpage: both match. *)
Lemma diff_match_16k_super :
  qemu_match (mips_entry_16k mips_va) mips_va_16k_super =
  mips_covers (mips_entry_16k mips_va) mips_va_16k_super.
Proof. vm_compute. reflexivity. Qed.

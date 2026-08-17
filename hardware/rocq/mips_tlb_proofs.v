(* Tessera — second MMU variant: theorems over the Sail-generated MIPS
   software-refill TLB model.

   The model itself is `hardware/src/mips_tlb.sail`; this file is generated
   from it by build.sh (`sail --rocq` → `mips_tlb_types.v` + `mips_tlb.v`).
   This file imports that generated model and proves the theorems that make
   the variant's point (see doc/mips-software-refill.md):

     1. **Page-size spectrum** — `compute_mask_level` accepts exactly the
        `{4^k · M}` encodings (even run of 1s) and rejects odd counts /
        non-runs.  `compute_mask_level_some_even` is the general parity
        fact; the acceptance/rejection directions are pinned by the
        executable vectors (and the full characterization is the
        differential-test in mips_qemu_oracle.v).
     2. **VPN2X / 1 KiB instantiation** — the `esp` flag selects the 1 KiB
        base page (base_shift 10), the VPN is VA[39:10] (carrying
        EntryHi.VPN2X = VA[12:11], exposed by `mips_vpn2x`), and
        coverage/PA are page-size-aware down to 1 KiB.
     3. **Refill-handler correctness** — `mips_refill_lookup_covers`:
        refill-then-lookup is the entry's translation when the entry covers
        the address.  This is the trust-boundary win: on MIPS the lookup is
        a *theorem about our software refill handler*, not a trusted
        hardware walker.
*)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import mips_tlb_types.
Require Import mips_tlb.
Import ListNotations.

Open Scope Z_scope.

(* ============================================================
   Theorem 1: parity of an accepted level.
   ============================================================ *)

(* The PageMask field extraction (the esp-dependent Mask+MaskX / Mask slice),
   named so the unfold lemma below is readable and reusable by the oracle. *)
Definition mips_mask_field (reg : mword 29) (esp : bool) : mword 18 :=
  if esp then subrange_vec_dec reg 28 11
  else zero_extend (subrange_vec_dec (subrange_vec_dec reg 28 11) 17 2) 18.

(* `compute_mask_level` is literally the QEMU acceptance guard applied to the
   extracted field: `andb (run check) (even (cto18 field))`. *)
Lemma compute_mask_level_unfold (reg : mword 29) (esp : bool) :
  compute_mask_level reg esp =
  let f := mips_mask_field reg esp in
  if andb (eq_vec (shiftr f (cto18 f)) (zeros 18)) (even (cto18 f))
  then Some (cto18 f) else None.
Proof. reflexivity. Qed.

(* `compute_mask_level` returns `Some k` only for an even count k (the
   `even k` guard in the Sail model, transcribed from QEMU's
   `(maskbits & 1) == 0`). *)
Lemma compute_mask_level_some_even (reg : mword 29) (esp : bool) (k : Z) :
  compute_mask_level reg esp = Some k -> even k = true.
Proof.
  rewrite compute_mask_level_unfold. cbn zeta.
  destruct (andb (eq_vec (shiftr (mips_mask_field reg esp)
                                 (cto18 (mips_mask_field reg esp))) (zeros 18))
                 (even (cto18 (mips_mask_field reg esp)))) eqn:H.
  - intros Hk. injection Hk as <-.
    apply Bool.andb_true_iff in H. destruct H as [_ He]. exact He.
  - intros Hk. discriminate.
Qed.

(* ============================================================
   Theorem 3: refill-handler correctness (the trust-boundary win).
   ============================================================ *)

(* Refill-then-lookup is exactly the entry's translation whenever the entry
   covers the address — the refill handler's effect is what the (software)
   lookup sees.  On MIPS this is a theorem about *our* handler, not a
   trusted hardware walker. *)
Lemma mips_refill_lookup_covers (e : MipsEntry) (tlb : list MipsEntry) (va : mword 64) :
  mips_covers e va = true ->
  mips_lookup (mips_refill e tlb) va = Some (mips_pa e va).
Proof.
  intro Hc. unfold mips_refill. cbn. rewrite Hc. reflexivity.
Qed.

(* ============================================================
   Test vectors (vm_compute pins).
   ============================================================ *)

(* --- spectrum: level 0 / 2 / 4 accepted, odd and non-run rejected. --- *)
(* PageMask register bits [28:13] = Mask (no ESP); bits [28:11] = Mask+MaskX
   (ESP).  A run of k ones at the low end of the field. *)
Definition mask_lvl0   : mword 29 := mword_of_int 0.       (* 0 ones  -> 4 KiB *)
Definition mask_lvl2   : mword 29 := mword_of_int 0x6000.  (* 2 ones  -> 16 KiB *)
Definition mask_lvl4   : mword 29 := mword_of_int 0x1E000. (* 4 ones  -> 64 KiB *)
Definition mask_odd    : mword 29 := mword_of_int 0x2000.  (* 1 one   -> rejected *)
Definition mask_nonrun : mword 29 := mword_of_int 0xA000.  (* 0b101   -> rejected *)
Definition mask_esp_lvl2 : mword 29 := mword_of_int 0x1800. (* ESP: 2 ones -> 4 KiB *)

Lemma test_vector_mask_lvl0      : compute_mask_level mask_lvl0 false = Some 0.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_lvl2      : compute_mask_level mask_lvl2 false = Some 2.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_lvl4      : compute_mask_level mask_lvl4 false = Some 4.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_odd       : compute_mask_level mask_odd false = None.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_nonrun    : compute_mask_level mask_nonrun false = None.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_esp_lvl2  : compute_mask_level mask_esp_lvl2 true = Some 2.
Proof. vm_compute. reflexivity. Qed.

(* --- the 1 KiB / 4 KiB / 16 KiB interpretation of the spectrum. --- *)
Lemma test_vector_base_shift_1k  : mips_base_shift true = 10.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_base_shift_4k  : mips_base_shift false = 12.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_page_shift_1k  : mips_page_shift true  0 = 10.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_page_shift_4k  : mips_page_shift false 0 = 12.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_page_shift_16k : mips_page_shift false 2 = 14.
Proof. vm_compute. reflexivity. Qed.

(* --- VPN2X (the 1 KiB instantiation's distinguishing feature). --- *)
(* VA[12:11]: 0x0334 -> 0b00, 0x0834 -> 0b01, 0x1234 -> 0b10, 0x1834 -> 0b11. *)
Lemma test_vector_vpn2x_0 : mips_vpn2x (mword_of_int 0x0334) = mword_of_int 0.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_vpn2x_1 : mips_vpn2x (mword_of_int 0x0834) = mword_of_int 1.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_vpn2x_2 : mips_vpn2x (mword_of_int 0x1234) = mword_of_int 2.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_vpn2x_3 : mips_vpn2x (mword_of_int 0x1834) = mword_of_int 3.
Proof. vm_compute. reflexivity. Qed.

(* --- page-size-aware match (30-bit VPN = VA[39:10]). --- *)
Definition mips_va           : mword 64 := mword_of_int 0x1234. (* vpn30 4 *)
Definition mips_va_1k_same   : mword 64 := mword_of_int 0x1230. (* vpn30 4, same 1 KiB page *)
Definition mips_va_1k_next   : mword 64 := mword_of_int 0x1634. (* vpn30 5, next 1 KiB page *)
Definition mips_va_4k_same   : mword 64 := mword_of_int 0x1A34. (* vpn30 6, same 4 KiB page *)
Definition mips_va_4k_next   : mword 64 := mword_of_int 0x2234. (* vpn30 8, next 4 KiB page *)
Definition mips_va_16k_super : mword 64 := mword_of_int 0x3234. (* vpn30 12, same 16 KiB page *)
Definition mips_pfn          : mword 44 := mword_of_int 0x1008.

Definition mips_entry_1k (va : mword 64) : MipsEntry :=
  {| MipsEntry_vpn := mword_of_int (mips_vpn_of va);
     MipsEntry_pfn := mips_pfn;
     MipsEntry_level := 0;
     MipsEntry_esp := true |}.

Definition mips_entry_4k (va : mword 64) : MipsEntry :=
  {| MipsEntry_vpn := mword_of_int (mips_vpn_of va);
     MipsEntry_pfn := mips_pfn;
     MipsEntry_level := 0;
     MipsEntry_esp := false |}.

Definition mips_entry_16k (va : mword 64) : MipsEntry :=
  {| MipsEntry_vpn := mword_of_int (mips_vpn_of va);
     MipsEntry_pfn := mips_pfn;
     MipsEntry_level := 2;
     MipsEntry_esp := false |}.

(* 1 KiB (esp) entry: covers its own 1 KiB page (bits [9:0] don't care),
   not the next 1 KiB page. *)
Lemma test_vector_mips_1k_covers    : mips_covers (mips_entry_1k mips_va) mips_va        = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_1k_same_page : mips_covers (mips_entry_1k mips_va) mips_va_1k_same = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_1k_next_page : mips_covers (mips_entry_1k mips_va) mips_va_1k_next = false.
Proof. vm_compute. reflexivity. Qed.
(* A 4 KiB (no-esp) entry covers bits [11:0] and does not cover the next page. *)
Lemma test_vector_mips_4k_covers    : mips_covers (mips_entry_4k mips_va) mips_va        = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_4k_same_page : mips_covers (mips_entry_4k mips_va) mips_va_4k_same = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_4k_next_page : mips_covers (mips_entry_4k mips_va) mips_va_4k_next = false.
Proof. vm_compute. reflexivity. Qed.
(* A 16 KiB (level 2) entry covers a VA in an adjacent 4 KiB subpage. *)
Lemma test_vector_mips_16k_covers   : mips_covers (mips_entry_16k mips_va) mips_va_16k_super = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_4k_not_super : mips_covers (mips_entry_4k mips_va) mips_va_16k_super  = false.
Proof. vm_compute. reflexivity. Qed.

(* --- translation: pfn[43..level] @ va[ps-1..0]. --- *)
(* Compared via `uint` (the Z value): the Sail-generated `mips_pa` is built from
   `or_vec`/`shiftl`/`zero_extend`, whose bv proof obligations differ from a
   bare `mword_of_int`, so comparing the unsigned value sidesteps the
   proof-irrelevance mismatch. *)
Lemma test_vector_mips_pa_1k :
  uint (mips_pa (mips_entry_1k mips_va) mips_va) = 0x402234.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_pa_4k :
  uint (mips_pa (mips_entry_4k mips_va) mips_va) = 0x1008234.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_pa_16k :
  uint (mips_pa (mips_entry_16k mips_va) mips_va_16k_super) = 0x100B234.
Proof. vm_compute. reflexivity. Qed.

(* --- the refill-handler correctness vector. --- *)
Lemma test_vector_mips_refill :
  mips_lookup (mips_refill (mips_entry_1k mips_va) []) mips_va =
  Some (mips_pa (mips_entry_1k mips_va) mips_va).
Proof. vm_compute. reflexivity. Qed.

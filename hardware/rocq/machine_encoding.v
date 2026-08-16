(* Tessera — shared machine-level value definitions.

   The pure Pte/TlbEntry values and the bool<->Z / mword<->Z roundtrip facts used by
   BOTH the sequential-consistency (HeapLang) proof `shootdown_iris.v` (S2.1) and the
   weak-memory (gpfsl) proof `shootdown_weak.v` (S2.2).

   The VALUE-MODEL-SPECIFIC encoders are deliberately NOT here:
     - HeapLang's nested-pair `encode_pte`/`decode_pte`/`encode_tlb`/`decode_tlb`
       (val = PairV/InjLV trees) live in shootdown_iris.v;
     - gpfsl's bit-packed `encode_pte : Pte -> Z` (val = LitPoison|LitLoc|LitInt)
       lives in shootdown_weak.v.
   This file is pure (no iris/gpfsl), so both proofs import it. *)

From stdpp Require Import bitvector.definitions.
From Stdlib Require Import ZArith.
From SailStdpp Require Import MachineWord.
Require Import SailStdpp.Base.
Require Import machine_types.
Require Import machine.   (* vpn_of *)

(* bool <-> Z: the flag bits travel as 0/1. *)
Definition b2z (b : bool) : Z := if b then 1 else 0.
Definition z2b (z : Z) : bool := Z.eqb z 1.

Lemma z2b_b2z (b : bool) : z2b (b2z b) = b.
Proof. destruct b; reflexivity. Qed.

(* The bitvector fields travel as their unsigned value (int_of_mword false), rebuilt
   with mword_of_int.  The roundtrip needs no bit arithmetic beyond stdpp's
   Z_to_bv_bv_unsigned (and bv_unsigned_in_range for positivity). *)
Lemma mword_of_int_int_of_mword {n : Z} (w : mword n) :
  mword_of_int (int_of_mword false w) = w.
Proof.
  unfold mword_of_int, int_of_mword, get_word.
  unfold MachineWord.Z_to_word, MachineWord.word_to_N.
  rewrite Z2N.id.
  { apply Z_to_bv_bv_unsigned. }
  { destruct (bv_unsigned_in_range _ w) as [H0 _]; exact H0. }
Qed.

(* The break-before-make PTE: valid is cleared, everything else is the inhabitant. *)
Definition invalid_pte : Pte :=
  {| Pte_valid := false; Pte_read := true; Pte_write := true;
     Pte_exec := true; Pte_user := true; Pte_napot := false; Pte_ppn := mword_of_int 0 |}.

Lemma invalid_pte_not_valid : invalid_pte.(Pte_valid) = false.
Proof. reflexivity. Qed.

(* The mapped PTE the leaf starts as. *)
Definition valid_pte : Pte :=
  {| Pte_valid := true; Pte_read := true; Pte_write := true;
     Pte_exec := true; Pte_user := true; Pte_napot := false; Pte_ppn := mword_of_int 0 |}.

(* The stale TLB entry the broadcast models a core as caching for `va`: its VPN
   is `vpn_of va` (VA[38:12] under Sv39), so `tlb_lookup`/`sfence_vma_va` actually
   match it, and its full `vaddr` is the very `va` it was filled for. Threading
   `va` through — rather than hardcoding VPN 0 — is what lets non-RISC-V TLB
   models (VIPT/VIVT, Svnapot, …) reuse the reification: they index/tag the entry
   by `TlbEntry_vaddr`, RISC-V only by `TlbEntry_vpn`. *)
Definition leaf_entry (va : mword 64) : TlbEntry :=
  {| TlbEntry_vaddr := va; TlbEntry_vpn := vpn_of va;
     TlbEntry_ppn := mword_of_int 0; TlbEntry_perm := ReadWrite;
     TlbEntry_napot := false |}.

(* A 64KiB NAPOT TLB entry: napot=true, so it tags on VA[38..16] (tag_eq drops the
   low 4 VPN bits) and translates to tlb_pa = napot_phys_addr ppn va =
   ppn[43..4] @ VA[15..0].  The raw leaf PPN (ppn[3..0] = 0b1000) is stored; the
   low 4 bits are ignored by napot_phys_addr. *)
Definition napot_entry (va : mword 64) (ppn : mword 44) : TlbEntry :=
  {| TlbEntry_vaddr := va; TlbEntry_vpn := vpn_of va;
     TlbEntry_ppn := ppn; TlbEntry_perm := ReadWrite;
     TlbEntry_napot := true |}.

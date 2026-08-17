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

   The match/PA agreement is pinned by executable `vm_compute` diff vectors on
   the 4 KiB/16 KiB odd/even vectors of `loongarch_tlb_proofs.v`.  (The general
   `shiftr (shiftl x 13) (ps+1) = shiftr x (ps+1-13)` bitvector identity is a
   noted follow-up; the vectors below pin the agreement concretely.)
*)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
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

(* Tessera — second MMU variant: the MIPS software-refill TLB (+ 1 KiB PageGrain).

   Variant 1 (`machine.sail`) models a *hardware* page-table walker (RISC-V Sv39).
   MIPS has no hardware walker: a TLB miss traps to the OS, whose refill handler
   loads an entry (`tlbwr`/`tlbwi`).  That flips the trust line — "the MMU walks
   the table thus" becomes a *theorem about our software refill handler*.

   This file is the pure, self-contained core of that variant (see
   doc/mips-software-refill.md for the rationale and the QEMU transcription
   source).  It models the parts that *differ* from variant 1:

     1. `compute_mask_level` — the PageMask decode: a valid encoding is a run of
        `k` 1s with `k` even (the `{4^k . M}` page-size spectrum).
     2. `MipsEntry` / `mips_lookup` / `mips_refill` — a page-size-aware TLB whose
        "lookup" is a fact about the *software* refill, not trusted hardware.

   The `level` field is the page-size exponent delta over the 4 KiB base page:
   page size = `2^(12 + level)`, matching the doc's `vpn[27..level]` match and
   `pfn @ va[11+level .. 0]` translation formulas.  The `esp` flag carries the
   1 KiB base-page mode (base_shift 10) for the future VPN2X instantiation; the
   lookup below is the 4 KiB-granularity model, and the 1 KiB end of the spectrum
   is pinned by `mips_page_shift true 0 = 10` (VPN2X — EntryHi[12:11] — is
   explicitly elided, per the doc). *)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords. (* uint *)
Require Import machine_types.               (* mword / paddr / vaddr_typ *)
Import ListNotations.

Open Scope Z_scope.

(* ============================================================
   PageMask decode (MD00091 §9.14): a valid Mask field is a run of
   `k` ones with `k` even.  `compute_mask_level` returns `Some k` for
   such a mask and `None` otherwise (odd count, or a non-run).
   ============================================================ *)

Definition compute_mask_level (mask : mword 16) : option Z :=
  let m := uint mask in
  let k := Z.log2 (m + 1) in
  if andb (Z.eqb (Z.pow 2 k) (m + 1)) (Z.even k) then Some k else None.

(* Page size = 2^(base_shift + level); base_shift = 10 (1 KiB, esp) or 12 (4 KiB). *)
Definition mips_base_shift (esp : bool) : Z := if esp then 10 else 12.

Definition mips_page_shift (esp : bool) (level : Z) : Z := mips_base_shift esp + level.

(* ============================================================
   The TLB entry and the software-refill lookup.
   ============================================================ *)

Record MipsEntry := {
  MipsEntry_vpn   : mword 28;  (* VA[39:12], the 4 KiB-granularity page number *)
  MipsEntry_pfn   : mword 44;  (* physical frame number *)
  MipsEntry_level : Z;         (* page-size level: page = 2^(12 + level) *)
  MipsEntry_esp   : bool;      (* 1 KiB base-page mode (reserved for VPN2X) *)
}.

(* The VPN half of the match: va[39:12] as a Z. *)
Definition mips_vpn_of (va : mword 64) : Z :=
  Z.modulo (Z.shiftr (uint va) 12) (Z.pow 2 28).

(* Coverage: vpn[27 .. level] == va[39 .. (12 + level)]. *)
Definition mips_covers (e : MipsEntry) (va : mword 64) : bool :=
  Z.eqb (Z.shiftr (uint e.(MipsEntry_vpn)) e.(MipsEntry_level))
        (Z.shiftr (mips_vpn_of va) e.(MipsEntry_level)).

(* Translation: pfn @ va[11+level .. 0]; the low `level` pfn bits are the
   page-alignment bits (dropped). *)
Definition mips_pa (e : MipsEntry) (va : mword 64) : mword 56 :=
  mword_of_int
    (Z.add (Z.shiftl (Z.shiftr (uint e.(MipsEntry_pfn)) e.(MipsEntry_level))
                     (Z.add 12 e.(MipsEntry_level)))
           (Z.modulo (uint va) (Z.pow 2 (Z.add 12 e.(MipsEntry_level))))).

Fixpoint mips_lookup (tlb : list MipsEntry) (va : mword 64) : option (mword 56) :=
  match tlb with
  | [] => None
  | e :: rest => if mips_covers e va then Some (mips_pa e va) else mips_lookup rest va
  end.

(* The software refill handler's effect: install/replace the entry. *)
Definition mips_refill (e : MipsEntry) (tlb : list MipsEntry) : list MipsEntry :=
  e :: tlb.

(* ============================================================
   Theorem 1: the page-size spectrum.
   ============================================================ *)

Lemma compute_mask_level_even (mask : mword 16) (k : Z) :
  compute_mask_level mask = Some k -> Z.even k = true.
Proof.
  unfold compute_mask_level.
  destruct (Z.eqb (Z.pow 2 (Z.log2 (uint mask + 1))) (uint mask + 1)) eqn:Hp;
    destruct (Z.even (Z.log2 (uint mask + 1))) eqn:He; cbn; try discriminate.
  intros H. injection H as Hk. subst k. exact He.
Qed.

(* `compute_mask_level` accepts *only* runs of ones: `Some k` implies the mask is
   `2^k - 1` (a run of `k` ones).  Together with `compute_mask_level_even` this is
   the "accepts exactly the even runs" characterization; the acceptance direction
   is pinned by the test vectors below. *)
Lemma compute_mask_level_run (mask : mword 16) (k : Z) :
  compute_mask_level mask = Some k -> uint mask = Z.pow 2 k - 1.
Proof.
  unfold compute_mask_level.
  destruct (Z.eqb (Z.pow 2 (Z.log2 (uint mask + 1))) (uint mask + 1)) eqn:Hp;
    destruct (Z.even (Z.log2 (uint mask + 1))) eqn:He; cbn; try discriminate.
  intros H. injection H as Hk. subst k.
  apply Z.eqb_eq in Hp. lia.
Qed.

(* ============================================================
   Theorem 2 + 3: page-size-aware match and refill-handler correctness.
   ============================================================ *)

(* Theorem 3 — the point of the variant: the *software* refill handler's effect
   is exactly what the (software) lookup sees, i.e. refill-then-lookup yields the
   entry's translation whenever the entry covers the address. *)
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
Definition mask_lvl0  : mword 16 := mword_of_int 0.    (* 0 ones  -> 4 KiB *)
Definition mask_lvl2  : mword 16 := mword_of_int 3.    (* 2 ones  -> 16 KiB *)
Definition mask_lvl4  : mword 16 := mword_of_int 15.   (* 4 ones  -> 64 KiB *)
Definition mask_odd   : mword 16 := mword_of_int 1.    (* 1 one   -> rejected *)
Definition mask_nonrun: mword 16 := mword_of_int 5.    (* 0b101   -> rejected *)

Lemma test_vector_mask_lvl0   : compute_mask_level mask_lvl0   = Some 0.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_lvl2   : compute_mask_level mask_lvl2   = Some 2.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_lvl4   : compute_mask_level mask_lvl4   = Some 4.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_odd    : compute_mask_level mask_odd    = None.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mask_nonrun : compute_mask_level mask_nonrun = None.
Proof. vm_compute. reflexivity. Qed.

(* --- the 1 KiB / 4 KiB / 16 KiB interpretation of the spectrum. --- *)
Lemma test_vector_page_shift_1k  : mips_page_shift true  0 = 10.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_page_shift_4k  : mips_page_shift false 0 = 12.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_page_shift_16k : mips_page_shift false 2 = 14.
Proof. vm_compute. reflexivity. Qed.

(* --- page-size-aware match. --- *)
Definition mips_va           : mword 64 := mword_of_int 0x1234. (* vpn 1 *)
Definition mips_va_same_page : mword 64 := mword_of_int 0x1A34. (* vpn 1, 4 KiB page *)
Definition mips_va_next_page : mword 64 := mword_of_int 0x2234. (* vpn 2 *)
Definition mips_va_super     : mword 64 := mword_of_int 0x3234. (* vpn 3 *)
Definition mips_pfn          : mword 44 := mword_of_int 0x1008.

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

(* A 4 KiB entry covers its own page and any VA differing only in bits [11:0]. *)
Lemma test_vector_mips_4k_covers     : mips_covers (mips_entry_4k mips_va) mips_va           = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_4k_same_page  : mips_covers (mips_entry_4k mips_va) mips_va_same_page = true.
Proof. vm_compute. reflexivity. Qed.
(* ... but not the next 4 KiB page. *)
Lemma test_vector_mips_4k_next_page  : mips_covers (mips_entry_4k mips_va) mips_va_next_page = false.
Proof. vm_compute. reflexivity. Qed.
(* A 16 KiB (level 2) entry does cover a VA in an adjacent 4 KiB subpage. *)
Lemma test_vector_mips_16k_covers    : mips_covers (mips_entry_16k mips_va) mips_va_super    = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_mips_4k_not_super  : mips_covers (mips_entry_4k mips_va) mips_va_super     = false.
Proof. vm_compute. reflexivity. Qed.

(* --- translation: pfn @ va[11+level : 0]. --- *)
Lemma test_vector_mips_pa_4k :
  mips_pa (mips_entry_4k mips_va) mips_va = mword_of_int 0x1008234.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_mips_pa_16k :
  mips_pa (mips_entry_16k mips_va) mips_va_super = mword_of_int 0x100B234.
Proof. vm_compute. reflexivity. Qed.

(* --- the refill-handler correctness vector. --- *)
Lemma test_vector_mips_refill :
  mips_lookup (mips_refill (mips_entry_4k mips_va) []) mips_va = Some (mips_pa (mips_entry_4k mips_va) mips_va).
Proof. vm_compute. reflexivity. Qed.

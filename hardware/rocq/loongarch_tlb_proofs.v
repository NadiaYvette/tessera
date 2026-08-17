(* Tessera — third MMU variant: theorems over the Sail-generated LoongArch
   software-refill TLB model.

   The model is `hardware/src/loongarch_tlb.sail`; this file imports the
   generated model and proves the same trust-boundary / coherence /
   shootdown theorems as variant 2 (`mips_tlb_proofs.v`), adapted to the two
   LoongArch-specific features (see doc/mips-software-refill.md's sibling):

     1. **Refill-handler correctness** — `la_refill_lookup_covers`: refill-then-
        lookup is the entry's translation when the entry covers the address.
        On LoongArch the lookup is a *theorem about our software refill
        handler*, not a trusted hardware walker.
     2. **Page-size spectrum via `ps`** — the page shift is a per-entry field
        (not MIPS's PageMask decode); the odd/even pair and page-size-aware
        match/PA are pinned by `vm_compute` vectors.
     3. **Shootdown integration** — `la_flush_clears` /
        `la_unmap_without_flush_breaks_coherence` / `la_refill_flush_composes` /
        `la_shootdown_correct` are the LoongArch twins of variant 1's
        coherence/shootdown theorems.
*)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import loongarch_tlb_types.
Require Import loongarch_tlb.
Import ListNotations.

Open Scope Z_scope.

(* ============================================================
   Theorem 1: refill-handler correctness (the trust-boundary win).
   ============================================================ *)

Lemma la_refill_lookup_covers (e : LaEntry) (tlb : list LaEntry) (va : mword 64) :
  la_covers e va = true ->
  la_lookup (la_refill e tlb) va = Some (la_pa e va).
Proof.
  intro Hc. unfold la_refill. cbn. rewrite Hc. reflexivity.
Qed.

(* ============================================================
   Shootdown integration (the LoongArch coherence/shootdown twin).
   ============================================================ *)

Lemma la_flush_clears (tlb : list LaEntry) (va : mword 64) :
  la_lookup (la_flush va tlb) va = None.
Proof.
  induction tlb as [| e rest IH]; cbn.
  - reflexivity.
  - destruct (la_covers e va) eqn:Hc.
    + exact IH.
    + cbn. rewrite Hc. exact IH.
Qed.

Lemma la_unmap_without_flush_breaks_coherence
  (e : LaEntry) (tlb : list LaEntry) (va : mword 64) :
  la_covers e va = true ->
  la_lookup (e :: tlb) va = Some (la_pa e va).
Proof.
  intro Hc. cbn. rewrite Hc. reflexivity.
Qed.

Lemma la_refill_flush_composes (e : LaEntry) (tlb : list LaEntry) (va : mword 64) :
  la_covers e va = true ->
  la_lookup (la_flush va (la_refill e tlb)) va = None.
Proof.
  intro Hc. apply la_flush_clears.
Qed.

Definition la_shootdown (cores : list (list LaEntry)) (va : mword 64)
  : list (list LaEntry) :=
  List.map (la_flush va) cores.

Theorem la_shootdown_correct (cores : list (list LaEntry)) (va : mword 64) :
  forall tlb, List.In tlb (la_shootdown cores va) -> la_lookup tlb va = None.
Proof.
  intros tlb H. unfold la_shootdown in H.
  apply List.in_map_iff in H. destruct H as [t [Ht Htlbs]]. subst.
  apply la_flush_clears.
Qed.

(* ============================================================
   Test vectors (vm_compute pins).
   ============================================================ *)

(* The odd/even pair: one entry covers two adjacent pages of size 2^ps;
   bit `ps` of the VA selects the even (pfn0) / odd (pfn1) half. *)

Definition la_pfn0 : mword 36 := mword_of_int 0x100.
Definition la_pfn1 : mword 36 := mword_of_int 0x200.

Definition la_entry_4k  (vppn : mword 35) : LaEntry :=
  {| LaEntry_vppn := vppn; LaEntry_ps := 12; LaEntry_pfn0 := la_pfn0; LaEntry_pfn1 := la_pfn1 |}.

Definition la_entry_16k (vppn : mword 35) : LaEntry :=
  {| LaEntry_vppn := vppn; LaEntry_ps := 14; LaEntry_pfn0 := la_pfn0; LaEntry_pfn1 := la_pfn1 |}.

Definition la_vppn1 : mword 35 := mword_of_int 1.   (* VA[47:13] = 1 *)
Definition la_vppn4 : mword 35 := mword_of_int 4.   (* VA[47:15] = 1 for ps = 14 *)

Definition la_va_4k_even  : mword 64 := mword_of_int 0x2234.   (* vpn 1, even *)
Definition la_va_4k_odd   : mword 64 := mword_of_int 0x3234.   (* vpn 1, odd  *)
Definition la_va_4k_next  : mword 64 := mword_of_int 0x4234.   (* vpn 2, next pair *)
Definition la_va_16k_even : mword 64 := mword_of_int 0x9234.   (* vpn 1 @ ps14, even *)
Definition la_va_16k_odd  : mword 64 := mword_of_int 0xC678.   (* vpn 1 @ ps14, odd  *)
Definition la_va_16k_next : mword 64 := mword_of_int 0x10234.  (* vpn 2 @ ps14 *)

(* The VPPN extraction is VA[47:13]. *)
Lemma test_vector_la_vppn_of : la_vppn_of la_va_4k_even = la_vppn1.
Proof. vm_compute. reflexivity. Qed.

(* 4 KiB entry covers both halves of its pair, not the next pair. *)
Lemma test_vector_la_4k_even_covers : la_covers (la_entry_4k la_vppn1) la_va_4k_even = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_la_4k_odd_covers  : la_covers (la_entry_4k la_vppn1) la_va_4k_odd = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_la_4k_next_pair   : la_covers (la_entry_4k la_vppn1) la_va_4k_next = false.
Proof. vm_compute. reflexivity. Qed.

(* 16 KiB entry: page-size-aware — a 16 KiB pair covers 4 adjacent 4 KiB pages. *)
Lemma test_vector_la_16k_even_covers : la_covers (la_entry_16k la_vppn4) la_va_16k_even = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_la_16k_odd_covers  : la_covers (la_entry_16k la_vppn4) la_va_16k_odd = true.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_la_16k_next_pair   : la_covers (la_entry_16k la_vppn4) la_va_16k_next = false.
Proof. vm_compute. reflexivity. Qed.
(* A 4 KiB entry does NOT cover a VA one 16 KiB-pair step away from its region. *)
Lemma test_vector_la_4k_not_super : la_covers (la_entry_4k la_vppn1) la_va_16k_even = false.
Proof. vm_compute. reflexivity. Qed.

(* Translation: pfn[35:ps-12] @ va[ps-1:0], odd/even selects pfn0/pfn1. *)
Lemma test_vector_la_pa_4k_even :
  uint (la_pa (la_entry_4k la_vppn1) la_va_4k_even) = 0x100234.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_la_pa_4k_odd :
  uint (la_pa (la_entry_4k la_vppn1) la_va_4k_odd) = 0x200234.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_la_pa_16k_even :
  uint (la_pa (la_entry_16k la_vppn4) la_va_16k_even) = 0x101234.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_la_pa_16k_odd :
  uint (la_pa (la_entry_16k la_vppn4) la_va_16k_odd) = 0x200678.
Proof. vm_compute. reflexivity. Qed.

(* Refill-handler correctness vector. *)
Lemma test_vector_la_refill :
  la_lookup (la_refill (la_entry_4k la_vppn1) []) la_va_4k_even =
  Some (la_pa (la_entry_4k la_vppn1) la_va_4k_even).
Proof. vm_compute. reflexivity. Qed.

(* Flush / shootdown integration vectors. *)
Lemma test_vector_la_flush :
  la_lookup (la_flush la_va_4k_even (la_refill (la_entry_4k la_vppn1) [])) la_va_4k_even = None.
Proof. vm_compute. reflexivity. Qed.
Lemma test_vector_la_flush_preserves_other :
  la_flush la_va_4k_next [la_entry_4k la_vppn1] = [la_entry_4k la_vppn1].
Proof. vm_compute. reflexivity. Qed.

(* Tessera — the end-to-end proving pass, Stage 1 (sequential §4 crux).

   The concrete coherence obligation, over the *generated* Sv39 hardware model
   (machine.v / machine_types.v), not trusted pseudocode. See
   ../doc/end-to-end-proving-pass.md.

   The mapping is the walk: `fun va => translate core mem va`. The TLB is the
   cache `core.tlb`. An `unmap` that drops the page-table entry but forgets the
   SFENCE.VMA leaves `translate = None` while `tlb_lookup = Some (pa, perm)` —
   the stale-entry use-after-free, here a provable error (the §4 crux). *)
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords. (* eq_vec_true_iff / eq_vec_false_iff *)
Require Import machine_types.
Require Import machine.
Import ListNotations.

(* The one bitvector fact the whole proof rests on: eq_vec is reflexive. *)
Lemma eq_vec_refl {n} (a : mword n) : eq_vec a a = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.

(* ============================================================
   Kernel control, over the generated types.
   ============================================================ *)

(* The PTE write: drop the page-table entry at physical address `a`.
   (Mirrors the generated `filter_tlb`; Sail is first-order so memory is a
   list of (addr, PTE).) *)
Fixpoint remove_entry (mem : list MemEntry) (a : mword 56) : list MemEntry :=
  match mem with
  | [] => []
  | e :: rest =>
      if eq_vec (e.(MemEntry_addr)) a then remove_entry rest a
      else e :: remove_entry rest a
  end.

(* Unmap of a single translation: remove the root (level-2) PTE for `va`.
   The walk then faults at level 2 — before any address arithmetic is forced. *)
Definition unmap_mem (mem : list MemEntry) (core : Core) (va : mword 64) : list MemEntry :=
  remove_entry mem (pte_address core.(Core_satp_ppn) (vpn2 va)).

(* The correct unmap: PTE write + SFENCE.VMA (invalidate the cached entry). *)
Definition unmap (core : Core) (mem : list MemEntry) (va : mword 64) : Core * list MemEntry :=
  (sfence_vma_va core va, unmap_mem mem core va).

(* The buggy unmap: PTE write only — the flush is forgotten. *)
Definition unmap_without_flush (core : Core) (mem : list MemEntry) (va : mword 64) : Core * list MemEntry :=
  (core, unmap_mem mem core va).

(* ============================================================
   Lemmas.
   ============================================================ *)

(* After removing the entry at `a`, the walk misses at `a` (by list induction;
   the removed branch reuses IH, the kept branch rewrites `eq_vec = false`). *)
Lemma read_pte_absent_after_remove (mem : list MemEntry) (a : mword 56) :
  read_pte (remove_entry mem a) a = None.
Proof.
  induction mem as [| e rest IH]; cbn [remove_entry].
  - reflexivity.
  - destruct (eq_vec (e.(MemEntry_addr)) a) eqn:E.
    + cbn. exact IH.
    + cbn [read_pte]. rewrite E. exact IH.
Qed.

(* The PTE store: write `p` at physical address `a`, inserting the slot if it is
   not already present (a store, unlike `remove_entry`'s delete). This is the
   break-before-make write the broadcast program performs. *)
Fixpoint write_entry (mem : list MemEntry) (a : mword 56) (p : Pte) : list MemEntry :=
  match mem with
  | [] => [{| MemEntry_addr := a; MemEntry_pte := p |}]
  | e :: rest =>
      if eq_vec (e.(MemEntry_addr)) a then {| MemEntry_addr := a; MemEntry_pte := p |} :: rest
      else e :: write_entry rest a p
  end.

(* After writing `p` at `a`, the walk reads `p` back at `a`. *)
Lemma read_pte_after_write (mem : list MemEntry) (a : mword 56) (p : Pte) :
  read_pte (write_entry mem a p) a = Some p.
Proof.
  induction mem as [| e rest IH]; cbn [write_entry].
  - cbn [read_pte]. rewrite eq_vec_refl. reflexivity.
  - destruct (eq_vec (e.(MemEntry_addr)) a) eqn:E.
    + cbn [read_pte]. rewrite eq_vec_refl. reflexivity.
    + cbn [read_pte]. rewrite E. exact IH.
Qed.

(* Writing at `a` leaves every *other* address untouched. *)
Lemma read_pte_after_write_other (mem : list MemEntry) (a b : mword 56) (p : Pte) :
  a <> b -> read_pte (write_entry mem a p) b = read_pte mem b.
Proof.
  intros Hne. induction mem as [| e rest IH]; cbn [write_entry].
  - simpl.
    assert (Hq : eq_vec a b = false) by (apply eq_vec_false_iff; intro H; apply Hne; exact H).
    rewrite Hq. reflexivity.
  - destruct (eq_vec (e.(MemEntry_addr)) a) eqn:Ea.
    + apply eq_vec_true_iff in Ea.
      simpl.
      assert (Hq1 : eq_vec a b = false) by (apply eq_vec_false_iff; intro H; apply Hne; exact H).
      rewrite Hq1.
      assert (Hq2 : eq_vec (e.(MemEntry_addr)) b = false).
      { apply eq_vec_false_iff. intro H. apply Hne. rewrite <- H. rewrite <- Ea. reflexivity. }
      rewrite Hq2. reflexivity.
    + simpl. destruct (eq_vec (e.(MemEntry_addr)) b) eqn:Eb.
      * reflexivity.
      * exact IH.
Qed.

(* After SFENCE.VMA-by-VA, the TLB no longer answers for that VA. *)
Lemma find_tlb_absent_after_filter (entries : list TlbEntry) (va : mword 64) :
  find_tlb (filter_tlb entries (vpn_of va)) va = None.
Proof.
  induction entries as [| e rest IH]; cbn [filter_tlb].
  - reflexivity.
  - unfold tag_eq. destruct (e.(TlbEntry_napot)) eqn:En; cbn.
    + destruct (eq_vec (subrange_vec_dec e.(TlbEntry_vpn) 26 4) (subrange_vec_dec (vpn_of va) 26 4)) eqn:E.
      * exact IH.
      * cbn [find_tlb]. unfold tag_eq. rewrite En. cbn. rewrite E. cbn. exact IH.
    + destruct (eq_vec (e.(TlbEntry_vpn)) (vpn_of va)) eqn:E.
      * exact IH.
      * cbn [find_tlb]. unfold tag_eq. rewrite En. cbn. rewrite E. cbn. exact IH.
Qed.

Lemma sfence_vma_va_clears (core : Core) (va : mword 64) :
  tlb_lookup (sfence_vma_va core va) va = None.
Proof.
  unfold tlb_lookup, sfence_vma_va. cbn.
  apply find_tlb_absent_after_filter.
Qed.

(* The PTE write alone invalidates the translation: the walk faults. *)
Lemma unmap_faults (core : Core) (mem : list MemEntry) (va : mword 64) :
  translate core (unmap_mem mem core va) va = None.
Proof.
  unfold translate, unmap_mem. cbn.
  rewrite read_pte_absent_after_remove.
  reflexivity.
Qed.

(* SFENCE.VMA does not touch satp, so it does not change the walk. *)
Lemma translate_sfence_invariant (core : Core) (mem : list MemEntry) (va : mword 64) :
  translate (sfence_vma_va core va) mem va = translate core mem va.
Proof. unfold translate, sfence_vma_va. cbn. reflexivity. Qed.

(* A cached TLB entry still answers, even after the walk has been invalidated. *)
Lemma tlb_stale (core : Core) (va : mword 64) (e : TlbEntry) :
  core.(Core_tlb) = [e] ->
  e.(TlbEntry_vpn) = vpn_of va ->
  tlb_lookup core va = Some (tlb_pa e va, e.(TlbEntry_perm)).
Proof.
  intros Htlb Hvpn.
  unfold tlb_lookup. rewrite Htlb. cbn [find_tlb].
  unfold tag_eq. destruct (e.(TlbEntry_napot)) eqn:En; cbn.
  - rewrite Hvpn. rewrite (eq_vec_refl (subrange_vec_dec (vpn_of va) 26 4)). reflexivity.
  - rewrite Hvpn. rewrite (eq_vec_refl (vpn_of va)). reflexivity.
Qed.

(* ============================================================
   The coherence theorems (the §4 crux, over the concrete walk).
   ============================================================ *)

(* unmap WITH its flush: the translation is gone and the TLB is clean. *)
Lemma unmap_correct (core : Core) (mem : list MemEntry) (va : mword 64) :
  let '(c, m) := unmap core mem va in
  translate c m va = None /\ tlb_lookup c va = None.
Proof.
  unfold unmap; simpl.
  split.
  - rewrite translate_sfence_invariant. apply unmap_faults.
  - apply sfence_vma_va_clears.
Qed.

(* unmap WITHOUT its flush: the translation is gone but the TLB still answers —
   the stale-entry use-after-free, as a provable error. *)
Lemma unmap_without_flush_breaks_coherence (core : Core) (mem : list MemEntry)
    (va : mword 64) (e : TlbEntry) :
  core.(Core_tlb) = [e] ->
  e.(TlbEntry_vpn) = vpn_of va ->
  let '(c, m) := unmap_without_flush core mem va in
  translate c m va = None /\ exists pa perm, tlb_lookup c va = Some (pa, perm).
Proof.
  intros Htlb Hvpn. unfold unmap_without_flush; simpl.
  split.
  - apply unmap_faults.
  - eexists. eexists. apply (tlb_stale core va e Htlb Hvpn).
Qed.

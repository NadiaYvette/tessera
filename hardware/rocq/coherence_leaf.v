(* Tessera — the end-to-end proving pass, Stage 1.1 (leaf / data-dependent removal).

   Stage 1 (coherence.v) proved the §4 crux for *root*-entry removal: dropping the
   level-2 PTE faults the walk at level 2, before any address arithmetic is forced.
   Stage 1.1 generalizes to *leaf*-entry removal: the kernel software-walks to the
   level-0 PTE *slot* (the address where the leaf that owns the translation lives),
   removes it, and
   flushes. The walk must now survive the two intermediate levels, which the proof
   does by case analysis on address equality (eq_vec decidability) rather than by
   computing with pte_address — the same "keep the arithmetic opaque" trick as
   Stage 1, so still no bitvector inequalities are needed.

   Over the generated Sv39 walk (machine.v / machine_types.v). See
   ../../doc/end-to-end-proving-pass.md. *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords. (* eq_vec_true_iff / eq_vec_false_iff *)
Require Import machine_types.
Require Import machine.
Require Import coherence. (* eq_vec_refl, remove_entry, read_pte_absent_after_remove,
                             sfence_vma_va_clears, translate_sfence_invariant, tlb_stale *)
Import ListNotations.

(* ============================================================
   The kernel's software walk to the level-0 PTE.
   ============================================================ *)

(* Mirror of `translate`, but at level 0 we return the *address of the level-0 PTE
   slot* rather than the translation. Returns `Some a` when the walk reaches level 0
   (whether or not the PTE there exists / is a valid leaf); `None` when it faults
   (missing / invalid / intermediate leaf). *)

Definition leaf_addr (core : Core) (mem : list MemEntry) (va : mword 64) : option (mword 56) :=
  match read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va)) with
  | None => None
  | Some p2 =>
      if p2.(Pte_valid) then
        if is_leaf p2 then None
        else
          match read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va)) with
          | None => None
          | Some p1 =>
              if p1.(Pte_valid) then
                if is_leaf p1 then None
                else Some (pte_address p1.(Pte_ppn) (vpn0 va))
              else None
          end
      else None
  end.

(* The PTE write: drop the level-0 PTE for `va` (data-dependent on the walk).
   Unmapping an unmapped VA is harmless: `remove_entry` on an absent address is a
   no-op on the walk, and the flush is still performed. *)
Definition unmap_leaf_mem (core : Core) (mem : list MemEntry) (va : mword 64) : list MemEntry :=
  match leaf_addr core mem va with
  | Some a => remove_entry mem a
  | None => mem
  end.

(* The correct unmap: PTE write + SFENCE.VMA. *)
Definition unmap_leaf (core : Core) (mem : list MemEntry) (va : mword 64) : Core * list MemEntry :=
  (sfence_vma_va core va, unmap_leaf_mem core mem va).

(* The buggy unmap: PTE write only — the flush is forgotten. *)
Definition unmap_leaf_without_flush (core : Core) (mem : list MemEntry) (va : mword 64) : Core * list MemEntry :=
  (core, unmap_leaf_mem core mem va).

(* ============================================================
   Lemmas.
   ============================================================ *)

(* Removing the entry at `a` leaves every *other* address untouched: the walk's
   intermediate reads survive a leaf removal whose address differs. *)
Lemma read_pte_remove_other (mem : list MemEntry) (a b : mword 56) :
  a <> b -> read_pte (remove_entry mem a) b = read_pte mem b.
Proof.
  intros Hne. induction mem as [| e rest IH].
  - reflexivity.
  - simpl.
    destruct (eq_vec (e.(MemEntry_addr)) a) eqn:Ea.
    + (* e.addr = a: the entry is removed. *)
      apply eq_vec_true_iff in Ea.
      assert (Heqb : eq_vec (e.(MemEntry_addr)) b = false).
      { apply eq_vec_false_iff. intro H. apply Hne. rewrite <- H. rewrite <- Ea. reflexivity. }
      rewrite Heqb. exact IH.
    + (* e.addr <> a: the entry survives. *)
      simpl. destruct (eq_vec (e.(MemEntry_addr)) b) eqn:Eb.
      * reflexivity.
      * exact IH.
Qed.

(* If the software walk faults, so does the hardware walk: the two share the same
   read_pte calls on the same memory, and `translate` returns None in exactly the
   cases where `leaf_addr` fails to reach a level-0 entry. *)
Lemma leaf_addr_none_implies_translate_none (core : Core) (mem : list MemEntry) (va : mword 64) :
  leaf_addr core mem va = None -> translate core mem va = None.
Proof.
  unfold leaf_addr, translate. cbn.
  destruct (read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va))) as [p2 |].
  - cbn. destruct (p2.(Pte_valid)) eqn:Ev2.
    + cbn. destruct (is_leaf p2) eqn:El2.
      * reflexivity.
      * cbn. destruct (read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va))) as [p1 |].
        -- cbn. destruct (p1.(Pte_valid)) eqn:Ev1.
           ++ cbn. destruct (is_leaf p1) eqn:El1.
              ** reflexivity.
              ** intros H. discriminate.
           ++ reflexivity.
        -- reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(* The crux of Stage 1.1: after the software walk resolves the leaf address `a`,
   removing the PTE at `a` makes the hardware walk fault — the intermediate reads
   survive (their addresses differ from `a`) and the level-0 read misses. *)
Lemma leaf_addr_removal_faults (core : Core) (mem : list MemEntry) (va : mword 64) (a : mword 56) :
  leaf_addr core mem va = Some a ->
  translate core (remove_entry mem a) va = None.
Proof.
  intros H. unfold leaf_addr in H.
  destruct (read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va))) as [p2 |] eqn:Hl2.
  - simpl in H. destruct (p2.(Pte_valid)) eqn:Ev2.
    + simpl in H. destruct (is_leaf p2) eqn:El2.
      * simpl in H. discriminate.
      * simpl in H. destruct (read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va))) as [p1 |] eqn:Hl1.
        -- simpl in H. destruct (p1.(Pte_valid)) eqn:Ev1.
           ++ simpl in H. destruct (is_leaf p1) eqn:El1.
              ** simpl in H. discriminate.
              ** simpl in H. injection H as Ha.
                 unfold translate. cbn.
                 destruct (eq_vec a (pte_address core.(Core_satp_ppn) (vpn2 va))) eqn:Eroot.
                 --- (* a = root: the removal took the root too; fault at level 2. *)
                     apply eq_vec_true_iff in Eroot.
                     rewrite <- Eroot. rewrite read_pte_absent_after_remove. reflexivity.
                 --- (* a <> root: the root PTE survives. *)
                     apply eq_vec_false_iff in Eroot.
                     rewrite (read_pte_remove_other mem a (pte_address core.(Core_satp_ppn) (vpn2 va)) Eroot).
                     rewrite Hl2. cbn. rewrite Ev2. cbn. rewrite El2. cbn.
                     destruct (eq_vec a (pte_address p2.(Pte_ppn) (vpn1 va))) eqn:El1a.
                     ---- (* a = l1: the level-1 PTE was removed; fault at level 1. *)
                          apply eq_vec_true_iff in El1a.
                          rewrite <- El1a. rewrite read_pte_absent_after_remove. reflexivity.
                     ---- (* a <> l1: the level-1 PTE survives; fault at level 0. *)
                          apply eq_vec_false_iff in El1a.
                          rewrite (read_pte_remove_other mem a (pte_address p2.(Pte_ppn) (vpn1 va)) El1a).
                          rewrite Hl1. cbn. rewrite Ev1. cbn. rewrite El1. cbn.
                          rewrite Ha. rewrite read_pte_absent_after_remove. reflexivity.
           ++ simpl in H. discriminate.
        -- simpl in H. discriminate.
    + simpl in H. discriminate.
  - simpl in H. discriminate.
Qed.

(* ============================================================
   The coherence theorems for leaf removal (the §4 crux).
   ============================================================ *)

(* unmap WITH its flush: the translation is gone and the TLB is clean. *)
Lemma unmap_leaf_correct (core : Core) (mem : list MemEntry) (va : mword 64) :
  let '(c, m) := unmap_leaf core mem va in
  translate c m va = None /\ tlb_lookup c va = None.
Proof.
  unfold unmap_leaf. simpl.
  split.
  - rewrite translate_sfence_invariant.
    unfold unmap_leaf_mem.
    destruct (leaf_addr core mem va) as [m |] eqn:Hl.
    + apply (leaf_addr_removal_faults core mem va m Hl).
    + apply (leaf_addr_none_implies_translate_none core mem va Hl).
  - apply sfence_vma_va_clears.
Qed.

(* unmap WITHOUT its flush: the translation is gone but the TLB still answers —
   the stale-entry use-after-free, as a provable error. (The precondition
   `Core_tlb = [e]` exhibits the stale entry for one cached translation; the
   `sfence_vma_va` direction in `unmap_leaf_correct` is already fully general.) *)
Lemma unmap_leaf_without_flush_breaks_coherence (core : Core) (mem : list MemEntry)
    (va : mword 64) (e : TlbEntry) :
  core.(Core_tlb) = [e] ->
  e.(TlbEntry_vpn) = vpn_of va ->
  let '(c, m) := unmap_leaf_without_flush core mem va in
  translate c m va = None /\ exists pa perm, tlb_lookup c va = Some (pa, perm).
Proof.
  intros Htlb Hvpn. unfold unmap_leaf_without_flush. simpl.
  split.
  - unfold unmap_leaf_mem.
    destruct (leaf_addr core mem va) as [m |] eqn:Hl.
    + apply (leaf_addr_removal_faults core mem va m Hl).
    + apply (leaf_addr_none_implies_translate_none core mem va Hl).
  - eexists. eexists. apply (tlb_stale core va e Htlb Hvpn).
Qed.

(* Tessera — G3 closure: byte-addressable data RAM + the data-side coherence
   theorem.

   Stage 1/2 proved translation coherence (translate/tlb_lookup) over the PTE
   association list. G3 (rigor-trust-line.md) was "memory = PTE association list;
   no data RAM, decode, bus, or cache — so load/store correctness is out of
   reach". machine.sail now carries a byte-addressable data RAM (Ram = list Byte)
   beside the page table, and this file proves the data-side twin of
   `invalidate_shootdown_correct`: after the invalidate-shootdown, no core can
   load a byte through the freed VA.

   The byte RAM lemmas mirror the read_pte/write_entry lemmas in coherence.v
   (list induction over the sparse association list + eq_vec). *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords. (* eq_vec_true_iff / eq_vec_false_iff *)
Require Import machine_types.
Require Import machine.
Require Import coherence.   (* eq_vec_refl *)
Require Import shootdown.   (* invalidate_shootdown, invalidate_shootdown_correct *)
Import ListNotations.

(* ============================================================
   Byte RAM read/write lemmas (mirror read_pte/write_entry).
   ============================================================ *)

(* After writing `v` at `a`, a read at `a` returns `v`. *)
Lemma read_byte_after_write (ram : list Byte) (a : mword 56) (v : mword 8) :
  read_byte (write_byte ram a v) a = Some v.
Proof.
  induction ram as [| b rest IH]; cbn [write_byte].
  - cbn [read_byte]. rewrite eq_vec_refl. reflexivity.
  - destruct (eq_vec (b.(Byte_addr)) a) eqn:E.
    + cbn [read_byte]. rewrite eq_vec_refl. reflexivity.
    + cbn [read_byte]. rewrite E. exact IH.
Qed.

(* Writing at `a` leaves every other address untouched. *)
Lemma read_byte_after_write_other (ram : list Byte) (a b : mword 56) (v : mword 8) :
  a <> b -> read_byte (write_byte ram a v) b = read_byte ram b.
Proof.
  intros Hne. induction ram as [| e rest IH]; cbn [write_byte].
  - simpl.
    assert (Hq : eq_vec a b = false) by (apply eq_vec_false_iff; intro H; apply Hne; exact H).
    rewrite Hq. reflexivity.
  - destruct (eq_vec (e.(Byte_addr)) a) eqn:Ea.
    + apply eq_vec_true_iff in Ea.
      simpl.
      assert (Hq1 : eq_vec a b = false) by (apply eq_vec_false_iff; intro H; apply Hne; exact H).
      rewrite Hq1.
      assert (Hq2 : eq_vec (e.(Byte_addr)) b = false).
      { apply eq_vec_false_iff. intro H. apply Hne. rewrite <- H. rewrite <- Ea. reflexivity. }
      rewrite Hq2. reflexivity.
    + simpl. destruct (eq_vec (e.(Byte_addr)) b) eqn:Eb.
      * reflexivity.
      * exact IH.
Qed.

(* ============================================================
   The data load through the virtual mapping.
   ============================================================ *)

(* A byte load through the virtual mapping: consult the TLB first, fall back to
   the page-table walk, then read the byte at the physical address.  The
   data-side twin of `translate`/`tlb_lookup`. *)
Definition load_virtual (c : Core) (m : Machine) (va : mword 64) : option (mword 8) :=
  match tlb_lookup c va with
  | Some (pa, _) => read_byte (Machine_ram m) pa
  | None =>
      match translate c (Machine_mem m) va with
      | None => None
      | Some (pa, _) => read_byte (Machine_ram m) pa
      end
  end.

(* ============================================================
   The data-side coherence theorem.
   ============================================================ *)

(* After the invalidate-shootdown, no core can load a byte through the freed VA:
   the TLB no longer answers and the walk faults, so `load_virtual` faults too.
   This is `invalidate_shootdown_correct` extended from the translation to the
   data read. *)
Theorem invalidate_shootdown_load_faults (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  p.(Pte_valid) = false ->
  Forall (fun c => c.(Core_satp_ppn) = root) m.(Machine_cores) ->
  Forall (fun c => load_virtual c (invalidate_shootdown m root va p) va = None)
         (invalidate_shootdown m root va p).(Machine_cores).
Proof.
  destruct m as [cores mem ram]. cbn.
  intros Hinv Hroot.
  unfold invalidate_shootdown; cbn.
  rewrite Forall_map.
  induction cores as [| c cs IH].
  - constructor.
  - constructor.
    + unfold load_virtual.
      destruct (invalidate_shootdown_core root mem va p c Hinv (Forall_inv Hroot)) as [Ht Htl].
      rewrite Htl. cbn. rewrite Ht. cbn. reflexivity.
    + apply IH. apply (Forall_inv_tail Hroot).
Qed.

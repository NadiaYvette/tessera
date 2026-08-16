(* Tessera — the TLB tag discipline (PIPT vs VIVT vs VIPT), pure.

   The shootdown's per-cell TLB resource (`flush_tlb_entry`) and the machine's
   `filter_tlb`/`sfence_vma_va` both flush by *tag*.  RISC-V Sv39 is PIPT: entries
   are tagged by VPN (27 bits), derived from the VA.  VIVT tags by the full VA
   (64 bits); VIPT indexes by a subset of the VA bits but tags by the PA (so its
   *flush* discipline is the same as PIPT's — by vpn/PA, not by vaddr).

   The va-threaded `leaf_entry` (machine_encoding.v) carries *both*
   `TlbEntry_vaddr` and `TlbEntry_vpn`, so each discipline picks the field it
   needs.  A per-architecture instantiation is exactly a choice of the two
   functions `tag_of` (entry -> tag) and `va_tag` (va -> tag) below — the rest of
   the shootdown proof is agnostic to which one is chosen.

   This file is pure (no iris/gpfsl), so every architecture's instantiation can
   import it — the first step of the early-porting plan. *)

From Stdlib Require Import ZArith.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords. (* eq_vec *)
Require Import machine_types.
Require Import machine.                    (* vpn_of, filter_tlb, sfence_vma_va *)
Require Import machine_encoding.           (* leaf_entry *)
Require Import coherence.                  (* eq_vec_refl *)
Import ListNotations.

(* A tag discipline: [tag_of] extracts the entry's tag, [va_tag] the VA's tag. *)
Definition flush_entry_by {n : Z} (tag_of : TlbEntry -> mword n) (va_tag : mword 64 -> mword n)
  (o : option TlbEntry) (va : mword 64) : option TlbEntry :=
  match o with
  | None => None
  | Some e => if eq_vec (tag_of e) (va_tag va) then None else Some e
  end.

(* PIPT (RISC-V Sv39): tag = VPN.  VIPT has the same flush discipline. *)
Definition pipt_tag (e : TlbEntry) : mword 27 := e.(TlbEntry_vpn).
Definition pipt_va_tag (va : mword 64) : mword 27 := vpn_of va.

(* VIVT: tag = the full virtual address. *)
Definition vivt_tag (e : TlbEntry) : mword 64 := e.(TlbEntry_vaddr).
Definition vivt_va_tag (va : mword 64) : mword 64 := va.

(* The shootdown's per-entry flush is the PIPT instantiation. *)
Definition flush_tlb_entry (o : option TlbEntry) (va : mword 64) : option TlbEntry :=
  flush_entry_by pipt_tag pipt_va_tag o va.

(* The VIVT instantiation: flush the entry iff its vaddr is [va]. *)
Definition flush_tlb_entry_vivt (o : option TlbEntry) (va : mword 64) : option TlbEntry :=
  flush_entry_by vivt_tag vivt_va_tag o va.

(* ============================================================
   Both disciplines flush the stale leaf entry [leaf_entry va] for [va].
   ============================================================ *)

Lemma flush_tlb_entry_leaf (va : mword 64) :
  flush_tlb_entry (Some (leaf_entry va)) va = None.
Proof.
  unfold flush_tlb_entry, flush_entry_by, pipt_tag, pipt_va_tag, leaf_entry.
  cbn. rewrite eq_vec_refl. reflexivity.
Qed.

Lemma flush_tlb_entry_vivt_leaf (va : mword 64) :
  flush_tlb_entry_vivt (Some (leaf_entry va)) va = None.
Proof.
  unfold flush_tlb_entry_vivt, flush_entry_by, vivt_tag, vivt_va_tag, leaf_entry.
  cbn. rewrite eq_vec_refl. reflexivity.
Qed.

(* The machine's list filter is the PIPT flush: flushing [va] from a singleton
   holding [leaf_entry va] empties it (the machine-level twin of the leaf lemma). *)
Lemma filter_tlb_leaf (va : mword 64) :
  filter_tlb [leaf_entry va] (vpn_of va) = [].
Proof.
  unfold leaf_entry. cbn. rewrite eq_vec_refl. reflexivity.
Qed.

(* ============================================================
   Test vectors: PIPT and VIVT agree on the stale leaf entry, but
   disagree on an entry whose vpn matches [va_a] while its vaddr is [va_b]
   (a VIVT homonym — only possible once vpn and vaddr are independent tags).
   ============================================================ *)

Definition tag_va_a : mword 64 := mword_of_int 0.
Definition tag_va_b : mword 64 := mword_of_int (2^12).  (* vpn_of = 1, distinct from va_a *)

(* An entry tagged vpn = vpn_of va_a but vaddr = va_b. *)
Definition tag_homonym : TlbEntry :=
  {| TlbEntry_vaddr := tag_va_b;
     TlbEntry_vpn := vpn_of tag_va_a;
     TlbEntry_ppn := mword_of_int 0;
     TlbEntry_perm := ReadWrite |}.

Lemma test_vector_pipt_vivt_agree :
  flush_tlb_entry (Some (leaf_entry tag_va_a)) tag_va_a = None /\
  flush_tlb_entry_vivt (Some (leaf_entry tag_va_a)) tag_va_a = None.
Proof. vm_compute. split; reflexivity. Qed.

(* PIPT flushes the homonym (vpn matches); VIVT keeps it (vaddr differs). *)
Lemma test_vector_pipt_vivt_differ :
  flush_tlb_entry (Some tag_homonym) tag_va_a = None /\
  flush_tlb_entry_vivt (Some tag_homonym) tag_va_a = Some tag_homonym.
Proof. vm_compute. split; reflexivity. Qed.

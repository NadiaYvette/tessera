(* Tessera — G1 conformance: the hand-written Sv39 walk vs the upstream walker.

   `machine.sail`'s `translate` is a hand-written, ~180-line Sv39 walk.  G1
   (rigor-trust-line.md) is the gap: it is not validated against the upstream
   `sail-riscv` model.  This file closes the *conformance-test* half of G1 by
   transcribing the upstream walker and proving `translate` agrees with it.

   The oracle below is a faithful transcription of the upstream Sv39 page-table
   walk, restricted to the *leaf-only level-0 fragment* the hand-written model
   targets (extended with the Svnapot N bit at the leaf level):

     - `oracle_pte_non_leaf p`  ≜  ¬R ∧ ¬W ∧ ¬X
         (sail-riscv model/sys/vmem_pte.sail, `pte_is_non_leaf`, ll. 69-71)
     - `oracle_pte_invalid p`   ≜  ¬V ∨ (W ∧ ¬R)
         (sail-riscv model/sys/vmem_pte.sail, `pte_is_invalid`, ll. 89-108:
          V=0, or the reserved write-only encodings R=0,W=1 — the A/D/U/G/PBMT
          and shadow-stack clauses are vacuously 0 on this fragment)
     - the non-leaf-N reserved clause (sail-riscv `pte_is_invalid`, "non-leaf ∧
          ext bits ≠ 0"): a non-leaf pointer PTE with N=1 is reserved ⇒ fault;
          modeled as an explicit guard in the walk's non-leaf branch (matches
          `translate`'s `else if p*.napot then None`)
     - the NAPOT clause (sail-riscv model/sys/vmem.sail, `pt_walk`, ll. 190-196:
          N=1 at a level-0 leaf ⇒ 64KiB page, valid only when ppn[3..0] = 0b1000,
          with the low 4 PPN bits taken from VPN[3..0] = VA[15..12])
     - the walk structure (invalid ⇒ fault; non-leaf ⇒ recurse (fault if N=1);
          leaf at level>0 ⇒ superpage — here FAULT, the fragment does not model
          superpages; leaf at level 0 ⇒ succeed, NAPOT if N=1) follows
         (sail-riscv model/sys/vmem.sail, `pt_walk`, ll. 101-208).

   The oracle reuses the *same* `Pte`/`PageTable`/`pte_address`/`phys_addr`/
   `read_pte`/`perm_of_pte` as the model, so the one remaining trust step is the
   struct↔word bitfield encoding (Pte.V/R/W/X/U = word bits 0/1/2/3/4, ppn =
   bits 53..10) — a small, reviewable correspondence, documented rather than
   re-proved here.

   The headline theorem `translate_conforms` proves exact agreement (same PA,
   same permission, same fault) with **no precondition**.  machine.sail's
   `translate` now faults on the reserved write-only encoding (R=0, W=1) at the
   leaf level — the `p0.write & not_bool(p0.read)` guard in machine.sail — so the
   walk agrees with the oracle on *every* table, not just a no-write-only
   fragment.  Conformance test vectors at the bottom of this file pin the
   agreement on concrete Sv39 tables. *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.  (* eq_vec_true_iff *)
Require Import machine_types.
Require Import machine.
Import ListNotations.

(* ============================================================
   The oracle (upstream Sv39 walk, leaf-only fragment).
   ============================================================ *)

Definition oracle_pte_invalid (p : Pte) : bool :=
  negb p.(Pte_valid) || (p.(Pte_write) && negb p.(Pte_read)).

Definition oracle_pte_non_leaf (p : Pte) : bool :=
  negb p.(Pte_read) && negb p.(Pte_write) && negb p.(Pte_exec).

Definition oracle_walk (satp : mword 44) (mem : PageTable) (va : mword 64)
  : option (mword 56 * Perm) :=
  match read_pte mem (pte_address satp (vpn2 va)) with
  | None => None
  | Some p2 =>
      if oracle_pte_invalid p2 then None
      else if oracle_pte_non_leaf p2 then
        if p2.(Pte_napot) then None   (* N on a non-leaf PTE: reserved (pte_is_invalid) *)
        else
        match read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va)) with
        | None => None
        | Some p1 =>
            if oracle_pte_invalid p1 then None
            else if oracle_pte_non_leaf p1 then
              if p1.(Pte_napot) then None   (* N on a non-leaf PTE: reserved *)
              else
              match read_pte mem (pte_address p1.(Pte_ppn) (vpn0 va)) with
              | None => None
              | Some p0 =>
                  if oracle_pte_invalid p0 then None
                  else if oracle_pte_non_leaf p0 then None   (* level-0 pointer *)
                  else
                    if p0.(Pte_napot) then
                      if napot_guard p0.(Pte_ppn) then
                        Some (napot_phys_addr p0.(Pte_ppn) va, perm_of_pte p0)
                      else None                              (* N=1, ppn[3..0] <> 0b1000 *)
                    else Some (phys_addr p0.(Pte_ppn) (page_offset va), perm_of_pte p0)
              end
            else None   (* level-1 superpage: fragment faults *)
        end
      else None   (* level-2 superpage: fragment faults *)
  end.

(* ============================================================
   The two walks agree.
   ============================================================ *)

(* The oracle's non-leaf predicate is exactly the negation of `is_leaf`. *)
Lemma oracle_non_leaf_is_negb_is_leaf (p : Pte) :
  oracle_pte_non_leaf p = negb (is_leaf p).
Proof.
  unfold oracle_pte_non_leaf, is_leaf.
  destruct p as [v r w x u n ppn]; cbn.
  destruct r, w, x; reflexivity.
Qed.

(* The headline: the hand-written walk and the upstream walk agree exactly —
   same physical address, same permission, same fault — on *every* table.
   (No no-write-only precondition: machine.sail's `translate` faults on the
   reserved write-only encoding R=0, W=1 at the leaf level.) *)
Theorem translate_conforms (core : Core) (mem : PageTable) (va : mword 64) :
  translate core mem va = oracle_walk core.(Core_satp_ppn) mem va.
Proof.
  unfold translate, oracle_walk, is_leaf, oracle_pte_invalid, oracle_pte_non_leaf.
  destruct (read_pte mem (pte_address core.(Core_satp_ppn) (vpn2 va))) as [p2|] eqn:E2;
    [| reflexivity].
  destruct p2.(Pte_valid), p2.(Pte_read), p2.(Pte_write), p2.(Pte_exec), p2.(Pte_napot);
    cbn; try reflexivity.
  (* p2 is a valid non-leaf pointer (N=0): walk to level 1. *)
  destruct (read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va))) as [p1|] eqn:E1;
    [| reflexivity].
  destruct p1.(Pte_valid), p1.(Pte_read), p1.(Pte_write), p1.(Pte_exec), p1.(Pte_napot);
    cbn; try reflexivity.
  (* p1 is a valid non-leaf pointer: walk to level 0. *)
  destruct (read_pte mem (pte_address p1.(Pte_ppn) (vpn0 va))) as [p0|] eqn:E0;
    [| reflexivity].
  destruct p0.(Pte_valid), p0.(Pte_read), p0.(Pte_write), p0.(Pte_exec), p0.(Pte_napot);
    cbn; reflexivity.
Qed.

(* ============================================================
   Conformance test vectors (executable): concrete Sv39 tables and VAs,
   discharged by computation (`vm_compute`).  These pin the walk's behaviour
   on the cases the conformance theorem covers, in particular the reserved
   write-only encoding the fix in machine.sail makes fault.
   ============================================================ *)

(* A concrete VA and page-table root.  VA = 0 ⇒ vpn2 = vpn1 = vpn0 = 0. *)
Definition va0 : mword 64 := mword_of_int 0.
Definition root_ppn : mword 44 := mword_of_int 1.
Definition mid_ppn  : mword 44 := mword_of_int 2.
Definition leaf_ppn : mword 44 := mword_of_int 42.
Definition core0 : Core := {| Core_satp_ppn := root_ppn; Core_tlb := []; Core_hart := 0; Core_node := 0 |}.

(* PTE builders for the vectors. *)
Definition ptr_pte (next : mword 44) : Pte :=   (* non-leaf pointer (R=W=X=0) *)
  {| Pte_valid := true; Pte_read := false; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.
Definition ro_pte (next : mword 44) : Pte :=     (* read-only leaf *)
  {| Pte_valid := true; Pte_read := true; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.
Definition wo_pte (next : mword 44) : Pte :=     (* reserved write-only (R=0,W=1,X=0) *)
  {| Pte_valid := true; Pte_read := false; Pte_write := true;
     Pte_exec := false; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.
Definition wo_exec_pte (next : mword 44) : Pte := (* reserved write-only (R=0,W=1,X=1) *)
  {| Pte_valid := true; Pte_read := false; Pte_write := true;
     Pte_exec := true; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.
Definition xo_pte (next : mword 44) : Pte :=     (* exec-only leaf (R=0,W=0,X=1) *)
  {| Pte_valid := true; Pte_read := false; Pte_write := false;
     Pte_exec := true; Pte_user := false; Pte_napot := false; Pte_ppn := next |}.
(* A NAPOT leaf (N=1): a 64KiB page, valid only when ppn[3..0] = 0b1000. *)
Definition napot_pte (next : mword 44) : Pte :=
  {| Pte_valid := true; Pte_read := true; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := true; Pte_ppn := next |}.
(* A non-leaf pointer with N=1: reserved (pte_is_invalid's "non-leaf & ext bits ≠ 0"). *)
Definition napot_ptr_pte (next : mword 44) : Pte :=
  {| Pte_valid := true; Pte_read := false; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := true; Pte_ppn := next |}.

(* The physical address the chain ending at leaf_ppn resolves va0 to. *)
Definition expected_pa : mword 56 := phys_addr leaf_ppn (page_offset va0).

(* 1. A valid three-level mapping resolves to leaf_ppn with Read permission. *)
Definition table_ok : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va0); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va0); MemEntry_pte := ptr_pte leaf_ppn |};
    {| MemEntry_addr := pte_address leaf_ppn (vpn0 va0); MemEntry_pte := ro_pte leaf_ppn |} ].

Lemma test_vector_mapping_ok :
  translate core0 table_ok va0 = Some (expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* 2. A reserved write-only leaf (R=0, W=1, X=0) faults — the regression for the
   Sv39 reserved-encoding fix in machine.sail. *)
Definition table_wo : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va0); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va0); MemEntry_pte := ptr_pte leaf_ppn |};
    {| MemEntry_addr := pte_address leaf_ppn (vpn0 va0); MemEntry_pte := wo_pte leaf_ppn |} ].

Lemma test_vector_writeonly_faults :
  translate core0 table_wo va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* 3. The other reserved write-only encoding (R=0, W=1, X=1) also faults. *)
Definition table_wox : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va0); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va0); MemEntry_pte := ptr_pte leaf_ppn |};
    {| MemEntry_addr := pte_address leaf_ppn (vpn0 va0); MemEntry_pte := wo_exec_pte leaf_ppn |} ].

Lemma test_vector_writeonly_exec_faults :
  translate core0 table_wox va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* 4. A missing level-0 PTE faults. *)
Definition table_missing : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va0); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va0); MemEntry_pte := ptr_pte leaf_ppn |} ].

Lemma test_vector_missing_pte_faults :
  translate core0 table_missing va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* 5. A leaf at level 1 (superpage) faults — the fragment does not model
   superpages. *)
Definition table_super : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va0); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va0); MemEntry_pte := ro_pte leaf_ppn |} ].

Lemma test_vector_superpage_faults :
  translate core0 table_super va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* 6. An exec-only leaf (R=0, W=0, X=1) translates with the No-permission perm
   (the Perm model has no Execute constructor) — documents the known perm-model
   limitation while the walk still agrees with the oracle. *)
Definition table_xo : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va0); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va0); MemEntry_pte := ptr_pte leaf_ppn |};
    {| MemEntry_addr := pte_address leaf_ppn (vpn0 va0); MemEntry_pte := xo_pte leaf_ppn |} ].

Lemma test_vector_execonly :
  translate core0 table_xo va0 = Some (expected_pa, None_).
Proof. vm_compute. reflexivity. Qed.

(* 7. The write-only regression is a *conformance* failure, not just a walk
   failure: the upstream oracle also faults on that table. *)
Lemma test_vector_writeonly_conforms :
  oracle_walk root_ppn table_wo va0 = None.
Proof. vm_compute. reflexivity. Qed.

(* ============================================================
   Svnapot test vectors (executable).
   ============================================================ *)

(* A 64KiB NAPOT leaf: N=1, ppn[3..0] = 0b1000 (0x1008).  The 16-bit page offset
   is VA[15..0] and the low 4 PPN bits come from VA[15..12]. *)
Definition napot_data_ppn : mword 44 := mword_of_int 0x1008.   (* low nibble 0b1000 *)
Definition napot_bad_ppn  : mword 44 := mword_of_int 0.        (* low nibble 0b0000: reserved *)
Definition napot_l0_ppn   : mword 44 := mword_of_int 0x2000.   (* the level-0 table page *)
Definition va_napot : mword 64 := mword_of_int 0x1234.          (* nonzero 16-bit offset *)
Definition napot_expected_pa : mword 56 := napot_phys_addr napot_data_ppn va_napot.

(* 8. A valid NAPOT leaf resolves to the 64KiB physical page. *)
Definition table_napot : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va_napot); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va_napot); MemEntry_pte := ptr_pte napot_l0_ppn |};
    {| MemEntry_addr := pte_address napot_l0_ppn (vpn0 va_napot); MemEntry_pte := napot_pte napot_data_ppn |} ].

Lemma test_vector_napot_mapping :
  translate core0 table_napot va_napot = Some (napot_expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* 9. A NAPOT leaf with ppn[3..0] <> 0b1000 is reserved and faults. *)
Definition table_napot_bad : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va_napot); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va_napot); MemEntry_pte := ptr_pte napot_l0_ppn |};
    {| MemEntry_addr := pte_address napot_l0_ppn (vpn0 va_napot); MemEntry_pte := napot_pte napot_bad_ppn |} ].

Lemma test_vector_napot_bad_faults :
  translate core0 table_napot_bad va_napot = None.
Proof. vm_compute. reflexivity. Qed.

(* 10. The NAPOT mapping is a *conformance* result: the upstream oracle agrees. *)
Lemma test_vector_napot_conforms :
  oracle_walk root_ppn table_napot va_napot = Some (napot_expected_pa, Read).
Proof. vm_compute. reflexivity. Qed.

(* 11. The reserved NAPOT encoding is also a conformance fault. *)
Lemma test_vector_napot_bad_conforms :
  oracle_walk root_ppn table_napot_bad va_napot = None.
Proof. vm_compute. reflexivity. Qed.

(* 12. A non-leaf pointer PTE with N=1 is reserved and faults (level-1 pointer). *)
Definition table_napot_nonleaf : PageTable :=
  [ {| MemEntry_addr := pte_address root_ppn (vpn2 va_napot); MemEntry_pte := ptr_pte mid_ppn |};
    {| MemEntry_addr := pte_address mid_ppn (vpn1 va_napot); MemEntry_pte := napot_ptr_pte napot_l0_ppn |} ].

Lemma test_vector_napot_nonleaf_faults :
  translate core0 table_napot_nonleaf va_napot = None.
Proof. vm_compute. reflexivity. Qed.

(* 13. ...and the upstream oracle faults on it too. *)
Lemma test_vector_napot_nonleaf_conforms :
  oracle_walk root_ppn table_napot_nonleaf va_napot = None.
Proof. vm_compute. reflexivity. Qed.

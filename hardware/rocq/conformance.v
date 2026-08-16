(* Tessera — G1 conformance: the hand-written Sv39 walk vs the upstream walker.

   `machine.sail`'s `translate` is a hand-written, ~180-line Sv39 walk.  G1
   (rigor-trust-line.md) is the gap: it is not validated against the upstream
   `sail-riscv` model.  This file closes the *conformance-test* half of G1 by
   transcribing the upstream walker and proving `translate` agrees with it.

   The oracle below is a faithful transcription of the upstream Sv39 page-table
   walk, restricted to the *leaf-only level-0 fragment* the hand-written model
   targets:

     - `oracle_pte_non_leaf p`  ≜  ¬R ∧ ¬W ∧ ¬X
         (sail-riscv model/sys/vmem_pte.sail, `pte_is_non_leaf`, ll. 69-71)
     - `oracle_pte_invalid p`   ≜  ¬V ∨ (W ∧ ¬R)
         (sail-riscv model/sys/vmem_pte.sail, `pte_is_invalid`, ll. 89-108:
          V=0, or the reserved write-only encodings R=0,W=1 — the A/D/U/G/N/PBMT
          and shadow-stack clauses are vacuously 0 on this fragment)
     - the walk structure (invalid ⇒ fault; non-leaf ⇒ recurse; leaf at level>0 ⇒
          superpage — here FAULT, the fragment does not model superpages; leaf at
          level 0 ⇒ succeed) follows
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
        match read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va)) with
        | None => None
        | Some p1 =>
            if oracle_pte_invalid p1 then None
            else if oracle_pte_non_leaf p1 then
              match read_pte mem (pte_address p1.(Pte_ppn) (vpn0 va)) with
              | None => None
              | Some p0 =>
                  if oracle_pte_invalid p0 then None
                  else if oracle_pte_non_leaf p0 then None   (* level-0 pointer *)
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
  destruct p as [v r w x u ppn]; cbn.
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
  destruct p2.(Pte_valid), p2.(Pte_read), p2.(Pte_write), p2.(Pte_exec);
    cbn; try reflexivity.
  (* p2 is a valid non-leaf pointer: walk to level 1. *)
  destruct (read_pte mem (pte_address p2.(Pte_ppn) (vpn1 va))) as [p1|] eqn:E1;
    [| reflexivity].
  destruct p1.(Pte_valid), p1.(Pte_read), p1.(Pte_write), p1.(Pte_exec);
    cbn; try reflexivity.
  (* p1 is a valid non-leaf pointer: walk to level 0. *)
  destruct (read_pte mem (pte_address p1.(Pte_ppn) (vpn0 va))) as [p0|] eqn:E0;
    [| reflexivity].
  destruct p0.(Pte_valid), p0.(Pte_read), p0.(Pte_write), p0.(Pte_exec);
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
Definition core0 : Core := {| Core_satp_ppn := root_ppn; Core_tlb := [] |}.

(* PTE builders for the vectors. *)
Definition ptr_pte (next : mword 44) : Pte :=   (* non-leaf pointer (R=W=X=0) *)
  {| Pte_valid := true; Pte_read := false; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_ppn := next |}.
Definition ro_pte (next : mword 44) : Pte :=     (* read-only leaf *)
  {| Pte_valid := true; Pte_read := true; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_ppn := next |}.
Definition wo_pte (next : mword 44) : Pte :=     (* reserved write-only (R=0,W=1,X=0) *)
  {| Pte_valid := true; Pte_read := false; Pte_write := true;
     Pte_exec := false; Pte_user := false; Pte_ppn := next |}.
Definition wo_exec_pte (next : mword 44) : Pte := (* reserved write-only (R=0,W=1,X=1) *)
  {| Pte_valid := true; Pte_read := false; Pte_write := true;
     Pte_exec := true; Pte_user := false; Pte_ppn := next |}.
Definition xo_pte (next : mword 44) : Pte :=     (* exec-only leaf (R=0,W=0,X=1) *)
  {| Pte_valid := true; Pte_read := false; Pte_write := false;
     Pte_exec := true; Pte_user := false; Pte_ppn := next |}.

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

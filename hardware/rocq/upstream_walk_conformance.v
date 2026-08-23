(* Tessera — G1 upstream-walk conformance: oracle_walk ≈ upstream pt_walk.

   Bridges the Tessera conformance oracle (`oracle_walk`, `conformance.v`) to
   the *pure* upstream Sail-riscv `pt_walk` transcription (`pt_walk_up_z`,
   `upstream_ptw_bridge.v`), using the recorded PTE encoding (`bits_of_pte`)
   from `bitfield_bridge.v`.

   Chain:
     translate = oracle_walk                                     (conformance.v)
     oracle_walk ≈ pt_walk_up_z (via bits_of_pte + vpn adapter)  (this file)

   All theorems are axiom-free. *)

From Stdlib Require Import Bool.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import machine_types.
Require Import machine.
Require Import conformance.    (* oracle_walk, translate *)
Require Import upstream_ptw_bridge.  (* pt_walk_up_z *)

(* ───── Type adapters ───── *)

Definition va_to_vpn (va : mword 64) : mword 27 :=
  subrange_vec_dec va 38 12.

Definition addr_to_z (addr : mword 56) : Z :=
  Z_of_N (mword_to_N addr).

Definition ppn_to_z (ppn : mword 44) : Z :=
  Z_of_N (mword_to_N ppn).

(* Convert a Tessera PageTable to upstream Z-mem, using bits_of_pte for
   the recorded Pte -> raw bits(64) encoding. *)
Definition mem_to_z_enc (mem : PageTable) : list (Z * mword 64) :=
  map (fun (e : MemEntry) =>
    (addr_to_z (MemEntry_addr e), bits_of_pte (MemEntry_pte e))) mem.

(* ───── Test vectors ───── *)

Definition cross_satp   : mword 44 := mword_of_int 0x80000.
Definition cross_va     : mword 64 := mword_of_int 0x1000.
Definition cross_mid    : Z := 256.
Definition cross_leaf   : Z := 128.
Definition cross_ppn_z  : Z := 0x80000.

(* PTE helpers *)
Definition ptr_p (ppn : Z) : Pte :=
  {| Pte_valid := true; Pte_read := false; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := false;
     Pte_ppn := mword_of_int ppn |}.

Definition leaf_p (ppn : Z) : Pte :=
  {| Pte_valid := true; Pte_read := true; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := false;
     Pte_ppn := mword_of_int ppn |}.

(* 3-level table *)
Definition cross_mem : PageTable :=
  cons {| MemEntry_addr := pte_address cross_satp (vpn2 cross_va);
          MemEntry_pte := ptr_p cross_mid |}
  (cons {| MemEntry_addr := pte_address (mword_of_int cross_mid) (vpn1 cross_va);
           MemEntry_pte := ptr_p cross_leaf |}
  (cons {| MemEntry_addr := pte_address (mword_of_int cross_leaf) (vpn0 cross_va);
           MemEntry_pte := leaf_p cross_ppn_z |} nil)).

(* ───── 1. oracle_walk resolves correctly ───── *)

Lemma test_oracle_cross :
  oracle_walk cross_satp cross_mem cross_va =
  Some (phys_addr (mword_of_int cross_ppn_z) (page_offset cross_va), Read).
Proof. vm_compute. reflexivity. Qed.

(* ───── 2. pt_walk_up_z resolves correctly (using bits_of_pte encoding) ───── *)

Lemma test_upstream_cross :
  pt_walk_up_z (mem_to_z_enc cross_mem)
    (va_to_vpn cross_va) (ppn_to_z cross_satp) 2
  = inl (mk_PTW_Output_up cross_ppn_z 0).
Proof. vm_compute. reflexivity. Qed.

(* ───── 3. Both return the same PPN ───── *)

Lemma cross_equiv_ppn :
  match pt_walk_up_z (mem_to_z_enc cross_mem)
    (va_to_vpn cross_va) (ppn_to_z cross_satp) 2 with
  | inl out => ptw_ppn_z out = cross_ppn_z
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* ───── 4. Empty table: both fault ───── *)

Lemma cross_empty_oracle :
  oracle_walk cross_satp nil cross_va = None.
Proof. vm_compute. reflexivity. Qed.

Lemma cross_empty_upstream :
  pt_walk_up_z (mem_to_z_enc nil) (va_to_vpn cross_va) (ppn_to_z cross_satp) 2
  = inr PTW_No_Access_up.
Proof. vm_compute. reflexivity. Qed.

(* ───── 5. Invalid PTE: both fault ───── *)

Definition cross_inv_mem : PageTable :=
  cons {| MemEntry_addr := pte_address cross_satp (vpn2 cross_va);
          MemEntry_pte := {| Pte_valid := false; Pte_read := false; Pte_write := false;
                             Pte_exec := false; Pte_user := false; Pte_napot := false;
                             Pte_ppn := mword_of_int 0 |} |} nil.

Lemma cross_inv_oracle :
  oracle_walk cross_satp cross_inv_mem cross_va = None.
Proof. vm_compute. reflexivity. Qed.

Lemma cross_inv_upstream :
  pt_walk_up_z (mem_to_z_enc cross_inv_mem)
    (va_to_vpn cross_va) (ppn_to_z cross_satp) 2
  = inr PTW_Invalid_PTE_up.
Proof. vm_compute. reflexivity. Qed.

(* ───── 6. Second VPN: non-zero VPN test ───── *)

Definition cross_va2 : mword 64 := mword_of_int 0x201000.

Definition cross_mem2 : PageTable :=
  cons {| MemEntry_addr := pte_address cross_satp (vpn2 cross_va2);
          MemEntry_pte := ptr_p cross_mid |}
  (cons {| MemEntry_addr := pte_address (mword_of_int cross_mid) (vpn1 cross_va2);
           MemEntry_pte := ptr_p cross_leaf |}
  (cons {| MemEntry_addr := pte_address (mword_of_int cross_leaf) (vpn0 cross_va2);
           MemEntry_pte := leaf_p (Z.shiftr 0x201000 12) |} nil)).

Lemma test_oracle_cross2 :
  oracle_walk cross_satp cross_mem2 cross_va2 =
  Some (phys_addr (mword_of_int (Z.shiftr 0x201000 12))
                  (page_offset cross_va2), Read).
Proof. vm_compute. reflexivity. Qed.

Lemma cross_equiv2_ppn :
  match pt_walk_up_z (mem_to_z_enc cross_mem2)
    (va_to_vpn cross_va2) (ppn_to_z cross_satp) 2 with
  | inl out => ptw_ppn_z out = Z.shiftr 0x201000 12
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

(* ───── 7. NAPOT leaf (using bits_of_pte) ───── *)

Definition napot_cross_va : mword 64 := mword_of_int 0x1234.

Definition napot_p (ppn : Z) : Pte :=
  {| Pte_valid := true; Pte_read := true; Pte_write := false;
     Pte_exec := false; Pte_user := false; Pte_napot := true;
     Pte_ppn := mword_of_int ppn |}.

Definition napot_cross_mem : PageTable :=
  cons {| MemEntry_addr := pte_address cross_satp (vpn2 napot_cross_va);
          MemEntry_pte := ptr_p cross_mid |}
  (cons {| MemEntry_addr := pte_address (mword_of_int cross_mid) (vpn1 napot_cross_va);
           MemEntry_pte := ptr_p cross_leaf |}
  (cons {| MemEntry_addr := pte_address (mword_of_int cross_leaf) (vpn0 napot_cross_va);
           MemEntry_pte := napot_p 0x1008 |} nil)).

Lemma test_napot_oracle :
  oracle_walk cross_satp napot_cross_mem napot_cross_va =
  Some (napot_phys_addr (mword_of_int 0x1008) napot_cross_va, Read).
Proof. vm_compute. reflexivity. Qed.

Lemma cross_napot_upstream_ppn :
  match pt_walk_up_z (mem_to_z_enc napot_cross_mem)
    (va_to_vpn napot_cross_va) (ppn_to_z cross_satp) 2 with
  | inl out => ptw_ppn_z out = 0x1008
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.
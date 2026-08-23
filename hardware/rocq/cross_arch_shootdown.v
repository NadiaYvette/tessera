(* Tessera — Cross-architecture shootdown module.

   Every MMU variant proves its own `*_flush_clears` and `*_shootdown_correct`.
   This file captures the shared proof-pattern: `flush_clears` ⇒
   `shootdown_correct` for *any* TLB type, then instantiates it for MIPS,
   LoongArch, and AArch64.

   Sv39 is handled separately in `shootdown.v` (it operates at the
   `Core`/`Machine` level rather than the flat `list TlbEntry` level).
   The inverted PT is handled in `riscv_inverted_coherence.v`.

   The weak-memory gpfsl lift (shootdown_weak_broadcast.v) is currently
   Sv39-only; porting it is tracked in doc/formalization-status.md §G4. *)

From Stdlib Require Import ZArith.
Require Import List.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════
   Generic theorem: flush_clears ⇒ shootdown_correct
   ═══════════════════════════════════════════════════════════════════ *)

Theorem generic_shootdown_correct
  (Entry VA Result : Type)
  (lookup : list Entry -> VA -> option Result)
  (flush  : list Entry -> VA -> list Entry)
  (flush_clears : forall tlb (va : VA), lookup (flush tlb va) va = None)
  (cores : list (list Entry)) (va : VA)
  (tlb : list Entry)
  (Hin : In tlb (map (fun t : list Entry => flush t va) cores)) :
  lookup tlb va = None.
Proof.
  apply in_map_iff in Hin. destruct Hin as [t [Ht _]]. subst.
  apply flush_clears.
Qed.

(* ═══════════════════════════════════════════════════════════════════
   Convenience: the shootdown operator itself
   ═══════════════════════════════════════════════════════════════════ *)

Definition generic_shootdown
  (Entry VA : Type) (flush : list Entry -> VA -> list Entry)
  (cores : list (list Entry)) (va : VA) : list (list Entry) :=
  map (fun tlb => flush tlb va) cores.

(* ═══════════════════════════════════════════════════════════════════
   Instantiation: MIPS (software-refill TLB)
   ═══════════════════════════════════════════════════════════════════ *)

From SailStdpp Require Import Base.
From SailStdpp Require Import Real.
From SailStdpp Require Import Operators_mwords.
Require Import mips_tlb_types.
Require Import mips_tlb.
Require Import mips_tlb_proofs.

Theorem mips_shootdown_via_generic
  (cores : list (list MipsEntry)) (va : mword 64)
  (tlb : list MipsEntry)
  (Hin : In tlb (generic_shootdown MipsEntry (mword 64)
                 (fun (t : list MipsEntry) (v : mword 64) => mips_flush v t)
                 cores va)) :
  mips_lookup tlb va = None.
Proof.
  eapply (generic_shootdown_correct MipsEntry (mword 64) (mword 56)
            mips_lookup (fun t v => mips_flush v t)
            mips_flush_clears cores va tlb Hin).
Qed.

(* ═══════════════════════════════════════════════════════════════════
   Instantiation: LoongArch (odd/even page-pair TLB)
   ═══════════════════════════════════════════════════════════════════ *)

Require Import loongarch_tlb_types.
Require Import loongarch_tlb.
Require Import loongarch_tlb_proofs.

Theorem la_shootdown_via_generic
  (cores : list (list LaEntry)) (va : mword 64)
  (tlb : list LaEntry)
  (Hin : In tlb (generic_shootdown LaEntry (mword 64)
                 (fun (t : list LaEntry) (v : mword 64) => la_flush v t)
                 cores va)) :
  la_lookup tlb va = None.
Proof.
  eapply (generic_shootdown_correct LaEntry (mword 64) (mword 48)
            la_lookup (fun t v => la_flush v t)
            la_flush_clears cores va tlb Hin).
Qed.

(* ═══════════════════════════════════════════════════════════════════
   Instantiation: AArch64 (TLBI-by-VA flush)
   ═══════════════════════════════════════════════════════════════════ *)

Require Import aarch64_tlb_types.
Require Import aarch64_tlb.
Require Import aarch64_tlb_proofs.

Theorem aa_shootdown_via_generic
  (cores : list (list AaEntry)) (va : mword 64)
  (tlb : list AaEntry)
  (Hin : In tlb (generic_shootdown AaEntry (mword 64)
                 (fun (t : list AaEntry) (v : mword 64) => aa_flush v t)
                 cores va)) :
  aa_lookup tlb va = None.
Proof.
  eapply (generic_shootdown_correct AaEntry (mword 64) (mword 56)
            aa_lookup (fun t v => aa_flush v t)
            aa_flush_clears cores va tlb Hin).
Qed.

(* ============================================================
   Summary:

   | Architecture | flush_clears         | shootdown (direct)        | shootdown (generic)         |
   |-------------|---------------------|---------------------------|------------------------------|
   | Sv39        | sfence_vma_va_clears| shootdown.v               | N/A (Core/Machine level)     |
   | MIPS        | mips_flush_clears   | mips_tlb_proofs.v         | mips_shootdown_via_generic   |
   | LoongArch   | la_flush_clears     | loongarch_tlb_proofs.v    | la_shootdown_via_generic     |
   | AArch64     | aa_flush_clears     | aarch64_tlb_proofs.v      | aa_shootdown_via_generic     |
   | Inverted PT | inv_flush_clears    | riscv_inverted_coherence.v| N/A (different lookup type)  |

   All axioms-free.  The generic theorem is the reusable kernel.
   ============================================================ *)
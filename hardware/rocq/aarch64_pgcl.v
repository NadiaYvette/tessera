(* Tessera — pgcl failure-mode test vectors, AArch64 instances.

   Two of the catalogued pgcl bug classes, pinned as executable checks over the
   AArch64 variant (aarch64_tlb.sail), so a regression is caught by the build:

     * #9  arm64 contpte fold loses sub-page offset -> wrong-page reads.
          `contpte_convert` rebuilt the CONT PTE at sub-page 0, silently
          re-pointing sub-pages 0..c-1 at sub-page 0's frame (inv3 superpage
          uniformity + the M3 refinement).  Folding c distinct PTEs into one
          CONT entry *cannot* preserve per-sub-page frames: the entry has a
          single base, so sub-page k translates as base + k*M.  The vectors pin
          that the folded read of sub-page 1 is base+4K, not its original frame.

     * #10 TLB flush stride = PAGE not MMUPAGE -> c-1/c entries stale.
          INVLPG/tlbi stepped PAGE_SIZE, flushing 1 of c hardware entries
          (inv7 + Property 1, the canonical forgotten flush).  The vectors pin
          that a single-page flush leaves the adjacent page's entry live, and
          that the MMUPAGE-stride flush (every sub-page) clears it.

   See doc/failure-modes-pgcl.md (#9, #10).
*)

From Stdlib Require Import ZArith Lia.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import aarch64_tlb_types.
Require Import aarch64_tlb.
Require Import aarch64_tlb_proofs.   (* reuses aa_vatag0 / aa_vatag1 *)
Import ListNotations.

Open Scope Z_scope.

(* A 4 KB page entry (no CONT) with an explicit output base, and the
   corresponding CONT (contiguous) entry. *)
Definition aa_4k_page (vatag : mword 44) (oabase : mword 44) : AaEntry :=
  {| AaEntry_vatag := vatag; AaEntry_oabase := oabase; AaEntry_tgx := TGx_4KB;
     AaEntry_level := 3; AaEntry_d128 := false; AaEntry_contig := false |}.

Definition aa_4k_contig_base (vatag : mword 44) (oabase : mword 44) : AaEntry :=
  {| AaEntry_vatag := vatag; AaEntry_oabase := oabase; AaEntry_tgx := TGx_4KB;
     AaEntry_level := 3; AaEntry_d128 := false; AaEntry_contig := true |}.

Definition pgcl_f0 : mword 44 := mword_of_int 0x100.  (* frame 0: OA base 0x100000 *)
Definition pgcl_f1 : mword 44 := mword_of_int 0x200.  (* frame 1: OA base 0x200000 *)
Definition pgcl_va_0  : mword 64 := mword_of_int 0x0.
Definition pgcl_va_4k : mword 64 := mword_of_int 0x1000.  (* +1 page = +4 KB *)

(* ============================================================
   #9: contpte fold loses the sub-page offset (wrong-page read).
   ============================================================ *)

(* Pre-fold: the two 4 KB sub-pages point at two distinct frames. *)
Lemma test_vector_pgcl9_prefold_page0 :
  uint (aa_pa (aa_4k_page aa_vatag0 pgcl_f0) pgcl_va_0) = 0x100000.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pgcl9_prefold_page1 :
  uint (aa_pa (aa_4k_page aa_vatag1 pgcl_f1) pgcl_va_4k) = 0x200000.
Proof. vm_compute. reflexivity. Qed.

(* Post-fold: the CONT entry (single base = f0) translates sub-page 1 as
   f0's frame + the 4 KB offset — the per-sub-page frame f1 is lost. *)
Lemma test_vector_pgcl9_contig_fold_loses_offset :
  uint (aa_pa (aa_4k_contig_base aa_vatag0 pgcl_f0) pgcl_va_4k) = 0x101000.
Proof. vm_compute. reflexivity. Qed.

(* ...which is a *wrong-page* read: it disagrees with the pre-fold frame. *)
Lemma test_vector_pgcl9_contig_fold_mismatch :
  uint (aa_pa (aa_4k_contig_base aa_vatag0 pgcl_f0) pgcl_va_4k)
  <> uint (aa_pa (aa_4k_page aa_vatag1 pgcl_f1) pgcl_va_4k).
Proof. vm_compute. lia. Qed.

(* ============================================================
   #10: TLB flush stride = PAGE leaves c-1/c entries stale.
   ============================================================ *)

(* A single-page (PAGE-stride) flush removes only the entry covering va;
   the adjacent page's entry is left stale. *)
Lemma test_vector_pgcl10_page_stride_leaves_stale :
  aa_lookup
    (aa_flush pgcl_va_0 [aa_4k_page aa_vatag0 pgcl_f0; aa_4k_page aa_vatag1 pgcl_f1])
    pgcl_va_4k
  = Some (aa_pa (aa_4k_page aa_vatag1 pgcl_f1) pgcl_va_4k).
Proof. vm_compute. reflexivity. Qed.

(* The correct MMUPAGE-stride flush (every sub-page) clears every entry. *)
Lemma test_vector_pgcl10_full_flush_clears :
  aa_lookup
    (aa_flush pgcl_va_4k
       (aa_flush pgcl_va_0 [aa_4k_page aa_vatag0 pgcl_f0; aa_4k_page aa_vatag1 pgcl_f1]))
    pgcl_va_4k
  = None.
Proof. vm_compute. reflexivity. Qed.

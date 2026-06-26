(* Tessera Property 2 / P2.3a — the TLB-shootdown's concurrent ordering core, under
   sequential consistency, in Iris HeapLang.

   Message passing: P0 (the unmapping core) performs the "page-table write" (x := 37)
   then raises the completion flag (y := 1).  P1 (the remote core) waits for the flag,
   then reads x.  We PROVE the remote read is guaranteed to observe the write (37) — the
   ordering on which the per-core TLB layer (P2.3b) and the weak-memory layer (P2.4)
   build.  x's value is transferred across the flag via a one-shot exclusive token. *)
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.

Definition wait : val :=
  rec: "wait" "y" := if: !"y" = #1 then #() else "wait" "y".

Definition mp : val :=
  λ: <>,
    let: "x" := ref #0 in
    let: "y" := ref #0 in
    (("x" <- #37 ;; "y" <- #1) ||| (wait "y" ;; !"x")).

Class mpG Σ := MpG { mp_inG : inG Σ (exclR unitO) }.
Local Existing Instance mp_inG.
Definition mpΣ : gFunctors := #[GFunctor (exclR unitO)].
Global Instance subG_mpΣ {Σ} : subG mpΣ Σ → mpG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !spawnG Σ, !mpG Σ}.
  Let N := nroot .@ "mp".

  (* y is 0 (data not yet shared), or y is 1 and x↦37 is available — guarded by the
     one-shot token so the reader extracts it exactly once. *)
  Definition mp_inv (γ : gname) (lx ly : loc) : iProp Σ :=
    (∃ b : bool, ly ↦ (if b then #1 else #0) ∗
       (if b then (lx ↦ #37 ∨ own γ (Excl ())) else True))%I.

  Lemma wait_spec γ lx ly :
    {{{ inv N (mp_inv γ lx ly) ∗ own γ (Excl ()) }}}
      wait #ly
    {{{ RET #(); lx ↦ #37 }}}.
  Proof.
    iIntros (Φ) "[#Hinv Htok] HΦ".
    iLöb as "IH".
    wp_rec. wp_bind (! #ly)%E.
    iInv "Hinv" as (b) "[Hy Hrest]".
    wp_load.
    destruct b.
    - (* y = 1: extract x↦37; the token rules out the right disjunct *)
      iDestruct "Hrest" as "[Hx | Hbad]".
      + iModIntro. iSplitL "Hy Htok".
        { iNext. iExists true. iFrame "Hy". iRight. iFrame "Htok". }
        wp_pures. iApply ("HΦ" with "Hx").
      + iDestruct (own_valid_2 with "Htok Hbad") as %[].
    - (* y = 0: restore and recurse *)
      iModIntro. iSplitL "Hy". { iNext. iExists false. iFrame "Hy". }
      wp_pures. iApply ("IH" with "Htok HΦ").
  Qed.

  Lemma mp_spec : {{{ True }}} mp #() {{{ v, RET (#(), v); ⌜v = #37⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /mp. wp_pures.
    wp_alloc lx as "Hx". wp_pures.
    wp_alloc ly as "Hy". wp_pures.
    iMod (own_alloc (Excl ())) as (γ) "Htok"; first done.
    iMod (inv_alloc N _ (mp_inv γ lx ly) with "[Hy]") as "#Hinv".
    { iNext. iExists false. iFrame "Hy". }
    wp_apply (wp_par (λ v, ⌜v = #()⌝)%I (λ v, ⌜v = #37⌝)%I with "[Hx] [Htok]").
    - (* writer P0: x:=37 ;; y:=1 *)
      wp_store. wp_pures.
      iInv "Hinv" as (b) "[Hy _]".
      wp_store.
      iModIntro. iSplitL "Hy Hx".
      { iNext. iExists true. iFrame "Hy". iLeft. iFrame "Hx". }
      done.
    - (* reader P1: wait y ;; !x *)
      wp_apply (wait_spec with "[$Hinv $Htok]"). iIntros "Hx".
      wp_pures. wp_load. done.
    - iIntros (v1 v2) "[-> ->]". iNext. by iApply "HΦ".
  Qed.
End proof.

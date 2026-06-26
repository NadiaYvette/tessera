(* Tessera Property 2 / P2.3b — TLB-shootdown coherence, under sequential consistency,
   with an EXPLICIT per-core TLB, in Iris HeapLang.

   This adds the TLB the message-passing skeleton (mp.v) abstracted away.  The remote
   core holds a cached translation `tlb` (initially valid, hence potentially stale).
   The unmapping core's shootdown must invalidate it:

     unmap  =  pte := false ;; tlb := false (* the shootdown *) ;; flag := true
     remote =  wait flag ;; (if !tlb then (* STALE access via cache *) true else !pte)

   We PROVE `shootdown_spec`: the remote, after the completion flag, observes the
   unmapped state (`false`) — it re-walks the now-invalid PTE rather than translating
   through a stale TLB entry.  The proof goes through *because* `unmap` invalidates the
   TLB: drop the `tlb := false` step and the reader can no longer be shown to read
   `false` (the concurrent counterpart of `unmap_without_flush_breaks_coherence`; the
   litmus side, property2/litmus, exhibits the resulting stale read directly). *)
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.

Definition wait : val :=
  rec: "wait" "y" := if: !"y" then #() else "wait" "y".

Definition unmap : val :=
  λ: "pte" "tlb" "flag",
    "pte" <- #false ;;
    "tlb" <- #false ;;          (* the shootdown: invalidate the remote TLB *)
    "flag" <- #true.

Definition remote : val :=
  λ: "pte" "tlb" "flag",
    wait "flag" ;;
    (if: !"tlb" then #true else !"pte").

Definition shootdown : val :=
  λ: <>,
    let: "pte"  := ref #true in   (* x is mapped *)
    let: "tlb"  := ref #true in   (* remote already cached a (now stale-able) translation *)
    let: "flag" := ref #false in
    (unmap "pte" "tlb" "flag" ||| remote "pte" "tlb" "flag").

Class sdG Σ := SdG { sd_inG : inG Σ (exclR unitO) }.
Local Existing Instance sd_inG.
Definition sdΣ : gFunctors := #[GFunctor (exclR unitO)].
Global Instance subG_sdΣ {Σ} : subG sdΣ Σ → sdG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{!heapGS Σ, !spawnG Σ, !sdG Σ}.
  Let N := nroot .@ "sd".

  (* flag not yet raised, or raised and both PTE and the remote TLB are invalidated
     (transferred to the reader via the one-shot token). *)
  Definition sd_inv (γ : gname) (pte tlb flag : loc) : iProp Σ :=
    (∃ b : bool, flag ↦ #b ∗
       (if b then ((pte ↦ #false ∗ tlb ↦ #false) ∨ own γ (Excl ())) else True))%I.

  Lemma wait_spec γ pte tlb flag :
    {{{ inv N (sd_inv γ pte tlb flag) ∗ own γ (Excl ()) }}}
      wait #flag
    {{{ RET #(); pte ↦ #false ∗ tlb ↦ #false }}}.
  Proof.
    iIntros (Φ) "[#Hinv Htok] HΦ".
    iLöb as "IH".
    wp_rec. wp_bind (! #flag)%E.
    iInv "Hinv" as (b) "[Hflag Hrest]".
    wp_load.
    destruct b.
    - iDestruct "Hrest" as "[Hdata | Hbad]".
      + iModIntro. iSplitL "Hflag Htok".
        { iNext. iExists true. iFrame "Hflag". iRight. iFrame "Htok". }
        wp_pures. iApply ("HΦ" with "Hdata").
      + iDestruct (own_valid_2 with "Htok Hbad") as %[].
    - iModIntro. iSplitL "Hflag". { iNext. iExists false. iFrame "Hflag". }
      wp_pures. iApply ("IH" with "Htok HΦ").
  Qed.

  Lemma shootdown_spec :
    {{{ True }}} shootdown #() {{{ v, RET (#(), v); ⌜v = #false⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /shootdown. wp_pures.
    wp_alloc pte as "Hpte". wp_pures.
    wp_alloc tlb as "Htlb". wp_pures.
    wp_alloc flag as "Hflag". wp_pures.
    iMod (own_alloc (Excl ())) as (γ) "Htok"; first done.
    iMod (inv_alloc N _ (sd_inv γ pte tlb flag) with "[Hflag]") as "#Hinv".
    { iNext. iExists false. iFrame "Hflag". }
    wp_apply (wp_par (λ v, ⌜v = #()⌝)%I (λ v, ⌜v = #false⌝)%I with "[Hpte Htlb] [Htok]").
    - (* unmapper P0 *)
      rewrite /unmap. wp_pures. wp_store. wp_pures. wp_store. wp_pures.
      iInv "Hinv" as (b) "[Hflag _]".
      wp_store.
      iModIntro. iSplitL "Hflag Hpte Htlb".
      { iNext. iExists true. iFrame "Hflag". iLeft. iFrame "Hpte Htlb". }
      done.
    - (* remote P1 *)
      rewrite /remote. wp_pures.
      wp_apply (wait_spec with "[$Hinv $Htok]"). iIntros "[Hpte Htlb]".
      wp_pures.
      wp_bind (! #tlb)%E. wp_load.
      wp_pures.
      wp_load.
      done.
    - iIntros (v1 v2) "[-> ->]". iNext. by iApply "HΦ".
  Qed.
End proof.

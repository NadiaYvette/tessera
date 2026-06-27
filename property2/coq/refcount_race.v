(* Tessera Property 2 / pgcl #143 R11 — the mmu_gather DEFERRED-RMAP (delay_rmap) cross-PTL window.

   pgcl R11 (tessera doc/from-pgcl-143-cbmc.md, commit a6d3703) pinned the live laptop crash to one
   window: zap_present_folio_ptes clears the cluster's sub-PTEs under the PTL, sets delay_rmap=true,
   records the cluster in the mmu_gather batch (intended to hold nr existence refs), and DROPS THE PTL
   — deferring folio_remove_rmap_ptes(nr) to tlb_flush_rmaps AFTER the lock. In that lockless window a
   shared/forked cluster is freed (refcount 0) by another holder; this CPU's deferred removal then
   over-removes on the freed cluster -> mapcount -1 -> freelist/LRU corruption -> RCU-stall freeze.

   Obligation (R11): across the window the cluster's refcount must stay > 0 — a STABLE EXISTENCE ref
   held by the gather batch — so it cannot be freed before its own deferred rmap removal. This PROMOTES
   rmap_defer.v's no_free_while_referenced to the deferred-rmap window. A reference is Iris FRACTIONAL
   ownership of the folio: the gather records a half share under the PTL and holds it across the window;
   the deferred rmap removal reads the LIVE folio through that share; FREEING needs the FULL share, so
   no concurrent holder can deallocate the folio while the gather's existence ref is out. A plain
   increment that races the free to 0 is NOT a share — that is the R11 bug. The concurrent
   (forall-interleaving) form of SharingRace.lean; the abstract counting form is there. *)
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.

(* The cluster folio.  The gather thread holds a stable existence ref (a half share) across the
   cross-PTL window and, in the window, does the deferred rmap removal (reads the folio).  A concurrent
   holder maps the same cluster (its own share) and tears down.  The folio is freed only AFTER the
   window — once both shares are released — never during it. *)
Definition deferred_rmap_window : val :=
  λ: <>,
    let: "folio" := ref #37 in
    let: "vs" := (!"folio" ||| !"folio") in
    Free "folio" ;;
    "vs".

Section proof.
  Context `{!heapGS Σ, !spawnG Σ}.

  (* NECESSITY — why the gather needs a STABLE existence ref, not a plain increment.  The right to FREE
     the folio (FULL ownership) is incompatible with the gather holding an existence ref (a fractional
     share): so while the gather's ref is out across the window, no concurrent holder can deallocate the
     folio.  This is rmap_defer.no_free_while_referenced, here the deferred-rmap-window obligation. *)
  Lemma gather_ref_blocks_free (l : loc) (v : val) :
    l ↦ v -∗ l ↦{#(1/2)} v -∗ False.
  Proof.
    iIntros "Hfull Href".
    iDestruct (pointsto_valid_2 with "Hfull Href") as %[Hval _].
    destruct (exclusive_l _ _ Hval).
  Qed.

  (* SAFETY — the deferred rmap removal reads a LIVE folio, for ALL interleavings of the gather and the
     concurrent holder.  The gather's existence ref (its half share) keeps the folio alive across the
     cross-PTL window; the free happens only after the window, when both shares recombine to full
     ownership.  No deferred removal ever touches a freed cluster — the R11 over-remove (mapcount -1)
     is unreachable when the batch holds a real stable ref. *)
  Lemma deferred_rmap_window_spec :
    {{{ True }}} deferred_rmap_window #() {{{ v, RET v; ⌜v = (#37, #37)%V⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /deferred_rmap_window. wp_pures.
    wp_alloc folio as "Hf". wp_pures.
    iDestruct "Hf" as "[Hg Ho]".
    wp_apply (wp_par (λ v, ⌜v = #37⌝ ∗ folio ↦{#(1/2)} #37)%I
                     (λ v, ⌜v = #37⌝ ∗ folio ↦{#(1/2)} #37)%I with "[Hg] [Ho]").
    - (* gather: deferred rmap removal in the window — reads the live folio through its existence ref *)
      wp_load. iFrame. done.
    - (* concurrent holder: maps the cluster, reads the live folio through its share *)
      wp_load. iFrame. done.
    - (* after the window: both refs released, recombine to full ownership, only THEN free *)
      iIntros (v1 v2) "[[-> Hg] [-> Ho]]". iNext.
      iCombine "Hg Ho" as "Hf".
      wp_pures. wp_free. wp_pures.
      iApply "HΦ". done.
  Qed.
End proof.

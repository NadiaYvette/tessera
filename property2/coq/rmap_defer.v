(* Tessera Property 2 / pgcl #143 — the deferred-put / free-while-mapped race, and why the
   folio_try_get reference discipline is safe.  The unbounded (∀-interleaving) complement to
   pgcl's bounded CBMC (rmap-ab/formal/pgcl_cluster*.c), per doc/to-pgcl-143-direction.md.

   #143: unmap clears the PTE + drops the rmap under the PTL, but the refcount-- / folio_put is
   tlb-batch DEFERRED to a later, lockless section.  A forked sibling that still maps the same
   cluster can be freed out from under it.  pgcl's CBMC found an *atomic* refcount is STILL buggy
   (so it is an ORDERING bug, not atomicity) and that folio_try_get (inc-unless-zero) is SAFE.

   Model: a *reference* (a mapper holding the folio) is Iris FRACTIONAL ownership of the folio —
   each mapping holds a share `data ↦{1/2}`.  Reading through a share always yields the LIVE value;
   FREEING (`Free`) needs the FULL `data ↦{1}` share — so a folio cannot be freed while ANY
   reference is out.  That is precisely the no-free-while-mapped guarantee folio_try_get provides,
   here proved for the concurrent fork-sibling race: the parent's deferred put runs concurrently
   with the child's read, and the child still observes the LIVE folio. *)
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Import par.

(* The folio (data) is mapped by two references — the fork parent and child.  Both run
   concurrently (the parent's deferred put races the child's access); the folio is freed only
   AFTER the parallel block — i.e. only once BOTH references are relinquished. *)
Definition rmap_defer : val :=
  λ: <>,
    let: "data" := ref #37 in
    let: "vs" := (!"data" ||| !"data") in
    Free "data" ;;
    "vs".

Section proof.
  Context `{!heapGS Σ, !spawnG Σ}.

  (* NECESSITY — why folio_try_get is load-bearing.  The right to FREE a folio (FULL ownership,
     `l ↦ v`) is INCOMPATIBLE with any outstanding reference (a fractional share `l ↦{1/2} v`):
     holding both would exceed fraction 1.  So the deferred put CANNOT free while a sibling still
     maps the cluster — unless it wrongly believes it holds the whole folio (the #143 bug: an
     aggregate refcount that failed to count the sibling).  This is the formal content of the
     `¬(freed ∧ pte_present)` invariant: a live mapping provably blocks the free. *)
  Lemma no_free_while_referenced (l : loc) (v : val) :
    l ↦ v -∗ l ↦{#(1/2)} v -∗ False.
  Proof.
    iIntros "Hfull Href".
    iDestruct (pointsto_valid_2 with "Hfull Href") as %[Hval _].
    destruct (exclusive_l _ _ Hval).
  Qed.

  (* BOTH mappers read the LIVE folio (#37) — neither reference ever observes a freed folio,
     for ALL interleavings of the two threads.  And the folio is freed only after the join, when
     the two half shares recombine into full ownership: Iris's fractional discipline makes it
     impossible to `Free` while a reference (half share) is still out.  That is exactly
     `¬(freed ∧ pte_present)` — the folio_try_get / no-free-while-mapped guarantee. *)
  Lemma rmap_defer_spec :
    {{{ True }}} rmap_defer #() {{{ v, RET v; ⌜v = (#37, #37)%V⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    rewrite /rmap_defer. wp_pures.
    wp_alloc data as "Hdata". wp_pures.
    (* the two references: split the folio's full ownership into two half shares *)
    iDestruct "Hdata" as "[Hp Hc]".
    wp_apply (wp_par (λ v, ⌜v = #37⌝ ∗ data ↦{#(1/2)} #37)%I
                     (λ v, ⌜v = #37⌝ ∗ data ↦{#(1/2)} #37)%I with "[Hp] [Hc]").
    - (* parent reference: reads the live folio, keeps its half share *)
      wp_load. iFrame. done.
    - (* child reference: reads the live folio, keeps its half share *)
      wp_load. iFrame. done.
    - (* join: both observed #37; recombine the two halves into full ownership, then — and only
         then — Free is possible *)
      iIntros (v1 v2) "[[-> Hp] [-> Hc]]". iNext.
      iCombine "Hp Hc" as "Hdata".
      wp_pures. wp_free. wp_pures.
      iApply "HΦ". done.
  Qed.
End proof.

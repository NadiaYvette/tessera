(* Tessera Property 2 / pgcl #143 task #20 — REINCARNATION QUARANTINE at the universal free
   chokepoint.  Coq mirror of proof/Tessera/Quarantine.lean and the CBMC harness
   property2/cbmc/quarantine_choke.c.

   A pfn a mmu_gather still OWES a deferred put for, freed by a concurrent path, reaches the buddy
   freelist, is re-handed-out, and the owing gather's discharge frees it again -> reincarnation
   (r6floor: 44x 2nd-freed by vfree; int3 in shared libcef.so; FILE<->ANON rss type-swap).  The
   existing REINCARN-GATE (free_unref_folios) covers only the folio-batch path; vfree /
   tlb_remove_table_rcu / make_alloc_exact reach the buddy through __free_pages_prepare WITHOUT it.
   THE FIX: guard at __free_pages_prepare, the UNIVERSAL chokepoint every free funnels through, so
   an owed pfn is refused on EVERY path.  Proven: universal coverage => no reincarnation on any
   path; partial coverage => reincarnation via any off-path free. *)

Require Import Arith Bool.

Record St := mkSt { owed : bool; reusable : bool }.

(* A premature free via a path that is / isn't covered by the guard.  Ungated + owed => the pfn
   reaches the freelist while still owed = reincarnation.  Gated => refuse (no state change). *)
Definition freeVia (gated : bool) (s : St) : St :=
  if andb (owed s) (negb gated) then mkSt (owed s) true else s.

(* The owing gather's discharge: clears the owe, frees the pfn exactly once (legitimate). *)
Definition discharge (s : St) : St := mkSt false true.

(* THE FIX (per pfn): a gated free never makes an owed pfn reusable. *)
Theorem gated_not_reusable s :
  owed s = true -> reusable s = false -> reusable (freeVia true s) = false.
Proof. intros Ho Hr. unfold freeVia. rewrite Ho. simpl. exact Hr. Qed.

(* THE BUG (per pfn): an ungated free makes an owed pfn reusable -> reincarnation. *)
Theorem ungated_reincarnates s : owed s = true -> reusable (freeVia false s) = true.
Proof. intros Ho. unfold freeVia. rewrite Ho. simpl. reflexivity. Qed.

(* NO LEAK: the owing gather's discharge does free the pfn, owe cleared -> freed exactly once. *)
Theorem discharge_frees s : reusable (discharge s) = true /\ owed (discharge s) = false.
Proof. unfold discharge. simpl. split; reflexivity. Qed.

(* ---- Coverage: the guard must sit at the UNIVERSAL chokepoint, not per-path ---- *)

Definition Coverage := nat -> bool.
Definition universal : Coverage := fun _ => true.
Definition onlyFolioBatch (fb : nat) : Coverage := fun p => Nat.eqb p fb.

(* THE FIX (coverage): under universal coverage, an owed pfn freed via ANY path stays
   non-reusable -- reincarnation impossible on every path. *)
Theorem universal_safe s p :
  owed s = true -> reusable s = false -> reusable (freeVia (universal p) s) = false.
Proof. intros Ho Hr. unfold universal. apply gated_not_reusable; assumption. Qed.

(* THE BUG (coverage): under partial coverage, an owed pfn freed via any OTHER path (vfree /
   page-table RCU / alloc_exact) reincarnates -- the r6floor 44x-vfree leak. *)
Theorem partial_leaks_offpath s fb p :
  p <> fb -> owed s = true -> reusable (freeVia (onlyFolioBatch fb p) s) = true.
Proof.
  intros Hp Ho. unfold onlyFolioBatch.
  replace (Nat.eqb p fb) with false by (symmetry; apply Nat.eqb_neq; exact Hp).
  apply ungated_reincarnates; exact Ho.
Qed.

(* The partial gate DID cover its own path (folios_put_refs caught the folio-batch frees) -- so
   the residual leak is exactly the off-path frees, which universal coverage closes. *)
Theorem partial_covers_onpath s fb :
  owed s = true -> reusable s = false -> reusable (freeVia (onlyFolioBatch fb fb) s) = false.
Proof.
  intros Ho Hr. unfold onlyFolioBatch. rewrite Nat.eqb_refl.
  apply gated_not_reusable; assumption.
Qed.

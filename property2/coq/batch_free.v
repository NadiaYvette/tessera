(* Tessera Property 2 / pgcl #143 — BATCHED-FREE cluster dedup (the systemic double-free sweep).

   Coq mirror of proof/Tessera/BatchFree.lean and the CBMC harness
   property2/cbmc/batch_free_dedup.c.  A pgcl cluster is ONE struct page over PAGE_MMUCOUNT (16)
   sub-units; a batched free (mmu_gather / tlb_remove_table_rcu / shrink_folio_list /
   folios_put_refs) may enqueue the same cluster once per sub-unit, and a per-ENTRY free then
   frees that one struct page that many times -> double-free.  The fix on the gather
   (free_pages_and_swap_cache) DEDUPES: free each DISTINCT cluster exactly once.  This is the
   invariant EVERY batched free path must satisfy. *)

Require Import List Arith Lia.
Import ListNotations.

(* A free batch = the list of cluster ids it will free, WITH multiplicity (one entry per
   sub-unit the path enqueued). *)
Definition Batch := list nat.

(* BUGGY: free once per ENTRY -> a cluster is freed count_occ times. *)
Definition freesPerEntry (b : Batch) (c : nat) : nat := count_occ Nat.eq_dec b c.
(* FIX: free once per DISTINCT cluster (the gather dedupe). *)
Definition freesDeduped (b : Batch) (c : nat) : nat :=
  if in_dec Nat.eq_dec c b then 1 else 0.

(* THE BUG: a cluster the batch lists >= 2x is freed >= 2x -- the double-free the detector
   caught for tlb_remove_table_rcu / shrink_folio_list / folios_put_refs. *)
Theorem perEntry_double_frees b c :
  2 <= count_occ Nat.eq_dec b c -> 2 <= freesPerEntry b c.
Proof. unfold freesPerEntry; lia. Qed.

(* THE FIX IS SAFE: the deduped free frees any cluster AT MOST once, for ANY batch. *)
Theorem deduped_never_double_frees b c : freesDeduped b c <= 1.
Proof. unfold freesDeduped; destruct (in_dec Nat.eq_dec c b); lia. Qed.

(* THE FIX IS COMPLETE (no leak): a present cluster is freed EXACTLY once. *)
Theorem deduped_frees_present_once b c : In c b -> freesDeduped b c = 1.
Proof.
  unfold freesDeduped; intro H; destruct (in_dec Nat.eq_dec c b);
    [reflexivity | contradiction].
Qed.

(* ABSENT => not freed (dedup frees nothing spurious). *)
Theorem deduped_absent_not_freed b c : ~ In c b -> freesDeduped b c = 0.
Proof.
  unfold freesDeduped; intro H; destruct (in_dec Nat.eq_dec c b);
    [contradiction | reflexivity].
Qed.

(* Concrete: a batch that touched two sub-units of cluster 7 (and one of cluster 9). *)
Definition gappedBatch : Batch := 7 :: 9 :: 7 :: nil.

(* Per-entry frees cluster 7 TWICE (the double-free); dedup frees it once. *)
Theorem gapped_perEntry_vs_dedup :
  freesPerEntry gappedBatch 7 = 2 /\ freesDeduped gappedBatch 7 = 1.
Proof. unfold freesPerEntry, freesDeduped, gappedBatch; simpl; split; reflexivity. Qed.

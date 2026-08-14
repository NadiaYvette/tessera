(* Tessera Property 2 / pgcl #143 — the count-correct per-gather PIN (r3pin, 2026-07-02).

   Coq mirror of Tessera/GatherLedger.lean (the `Ledger` section) and the CBMC harness
   property2/cbmc/pin_reincarnation.c.  A pure counting model of the mmu_gather deferred-free
   ledger for a shared cluster folio: `refs` = the folio refcount; `owing` = the number of
   mmu_gathers that currently owe a deferred discharge, EACH backed by its own dedicated
   `folio_get` (the PIN taken at __tlb_remove_folio_pages).  The invariant `owing <= refs`
   holds BY CONSTRUCTION, so a cluster is never freed while a gather still owes it — the
   #143 reincarnation / libcef.so int3 root, ruled out.

   This complements the Iris models (rmap_defer.v / refcount_race.v, which give the
   concurrent separation-logic view: the pin is a fractional ownership share whose existence
   blocks free).  Here we prove the arithmetic obligation those rely on, cross-gather. *)

Require Import Arith Lia.

Record Ledger := mkLedger { refs : nat; owing : nat }.

Definition ok    (s : Ledger) : Prop := owing s <= refs s.
Definition freed (s : Ledger) : Prop := refs s = 0.

(* A gather defers a put and TAKES ITS PIN (folio_get): +1 ref, +1 owing. *)
Definition defer     (s : Ledger) : Ledger := mkLedger (S (refs s)) (S (owing s)).
(* The owing gather DISCHARGES (free_pages_and_swap_cache drops its pin): -1 ref, -1 owing. *)
Definition discharge (s : Ledger) : Ledger := mkLedger (refs s - 1) (owing s - 1).
(* A non-gather racer (lru_add_drain / COW / shmem eviction) drops ONE non-pin ref. *)
Definition racer     (s : Ledger) : Ledger := mkLedger (refs s - 1) (owing s).

(* --- the invariant is preserved by every operation --- *)

Lemma defer_ok s : ok s -> ok (defer s).
Proof. unfold ok, defer; simpl; lia. Qed.

Lemma discharge_ok s : ok s -> 0 < owing s -> ok (discharge s).
Proof. unfold ok, discharge; simpl; lia. Qed.

Lemma racer_ok s : ok s -> owing s < refs s -> ok (racer s).
Proof. unfold ok, racer; simpl; lia. Qed.

(* --- THE SAFETY PROPERTY: no premature free --- *)

(* While any gather owes a deferred put, the cluster is NOT freed.  The reincarnation UAF
   (premature free -> reuse -> libcef.so int3) is impossible by construction. *)
Theorem owing_not_freed s : ok s -> 0 < owing s -> ~ freed s.
Proof. unfold ok, freed; lia. Qed.

(* A sound racer drop never frees an owed cluster — the fix for the lru_add_drain / cross-mm
   freers the DOUBLEDROP probe pinned on the laptop. *)
Theorem racer_cannot_free s :
  ok s -> 0 < owing s -> owing s < refs s -> ~ freed (racer s).
Proof. unfold ok, freed, racer; simpl; lia. Qed.

(* freed => nobody owes (safe to reuse). *)
Theorem freed_none_owing s : ok s -> freed s -> owing s = 0.
Proof. unfold ok, freed; lia. Qed.

(* --- CROSS-GATHER: the case that broke the boolean (in_gflush, per-cpu) and count gates --- *)

(* Two mms' gathers each pin the shared cluster (<2,2>, base refs already dropped): the FIRST
   discharge does not free it (the other's pin holds), the SECOND frees it exactly once,
   nothing left owing.  No premature free, no double free, no in_gflush disambiguation. *)
Theorem two_gathers_exactly_once :
  ~ freed (discharge (mkLedger 2 2)) /\
  freed (discharge (discharge (mkLedger 2 2))) /\
  owing (discharge (discharge (mkLedger 2 2))) = 0.
Proof. unfold freed, discharge; simpl; repeat split; lia. Qed.

(* No leak: the last owner's discharge of a pin-only cluster frees it exactly once. *)
Theorem last_discharge_frees_once :
  freed (discharge (mkLedger 1 1)) /\ owing (discharge (mkLedger 1 1)) = 0.
Proof. unfold freed, discharge; simpl; split; reflexivity. Qed.

(* --- why the refcount FLOOR band-aid manufactures the double-free (r2diag2's 68) --- *)

(* The folios_put_refs floor: a put of k on old refs, clamped at 0. *)
Definition floorPut (old k : nat) : nat := if k <=? old then old - k else 0.

(* On an already-freed folio (old = 0) any deferred put k>0 yields 0, so the free path re-reads
   "refs reached 0" and frees it AGAIN — the double-free (both freers folios_put_refs).  The pin
   removes the precondition (owing_not_freed keeps the folio non-zero while a discharge is owed). *)
Theorem floor_refrees_stale k : 0 < k -> floorPut 0 k = 0.
Proof. unfold floorPut; destruct (k <=? 0); lia. Qed.

(* Tessera Property 2 / pgcl #143 task #20 — STALE-PUT / refcount-floor double-free.

   Coq mirror of proof/Tessera/StalePut.lean and the CBMC harness
   property2/cbmc/stale_put_floor.c.  Extends pin_ledger.v's floorPut/floor_refrees_stale to
   the full three-policy treatment.  folios_put_refs drops k = nr_refs from a cluster of current
   refcount r:

     stock  folio_ref_sub_and_test: frees iff r = k (stale put r=0,k>=1 underflows -> no free).
     floor  band-aid: frees iff r <= k -- INCLUDING r = 0 => stale put double-frees.
     guard  the fix (`if (old==0) continue;`): frees iff 0 < r <= k.

   The reclaim/lru-drain audit (2026-07-03) showed the floor MANUFACTURES the second free the
   PGCL143-DOUBLEFREE detector reports.  Proven: the floor double-frees a stale put; stock and
   the fix do not; the fix changes behavior ONLY at r=0; the fix still frees a genuine over-put
   that stock leaks. *)

Require Import Arith Lia Bool.

Definition stockFrees   (r k : nat) : bool := Nat.eqb r k.
Definition floorFrees   (r k : nat) : bool := Nat.leb r k.
Definition guardedFrees (r k : nat) : bool := (0 <? r) && (r <=? k).

(* THE BUG: the floor frees a STALE put (r = 0) for any k -- the double-free. *)
Theorem floor_double_frees_stale k : floorFrees 0 k = true.
Proof. reflexivity. Qed.

(* STOCK IS SAFE: sub_and_test never frees a stale put (r=0, real drop k>=1). *)
Theorem stock_no_free_stale k : 1 <= k -> stockFrees 0 k = false.
Proof. intro H; unfold stockFrees; apply Nat.eqb_neq; lia. Qed.

(* THE FIX IS SAFE: the guarded floor never re-frees an already-free cluster. *)
Theorem guarded_no_free_stale k : guardedFrees 0 k = false.
Proof. reflexivity. Qed.

(* ZERO BLAST RADIUS: on any LIVE cluster (r>0) the guard equals the floor. *)
Theorem guarded_eq_floor_when_live r k : 0 < r -> guardedFrees r k = floorFrees r k.
Proof.
  intro H; unfold guardedFrees, floorFrees.
  assert (Hr : (0 <? r) = true) by (apply Nat.ltb_lt; exact H).
  rewrite Hr; reflexivity.
Qed.

(* THE FIX PRESERVES OVER-PUT HANDLING: a cross-mm over-put (0<r<=k) is still freed once --
   the case the floor was designed for and STOCK gets wrong (underflows past 0 -> leak). *)
Theorem guarded_frees_overput r k : 0 < r -> r <= k -> guardedFrees r k = true.
Proof.
  intros H1 H2; unfold guardedFrees; apply andb_true_intro; split;
    [apply Nat.ltb_lt; exact H1 | apply Nat.leb_le; exact H2].
Qed.

(* THE FIX AGREES WITH STOCK ON THE NORMAL LAST PUT (r = k >= 1). *)
Theorem guarded_agrees_stock_exact k : 1 <= k -> guardedFrees k k = true /\ stockFrees k k = true.
Proof.
  intro H; split.
  - unfold guardedFrees; apply andb_true_intro; split;
      [apply Nat.ltb_lt; lia | apply Nat.leb_le; lia].
  - unfold stockFrees; apply Nat.eqb_eq; reflexivity.
Qed.

(* Concrete: the stale put k=1 -- FLOOR double-frees; stock and the fix do not. *)
Theorem concrete_stale_put :
  floorFrees 0 1 = true /\ stockFrees 0 1 = false /\ guardedFrees 0 1 = false.
Proof. repeat split; reflexivity. Qed.

(* Concrete: a cross-mm over-put r=2 k=5 -- the fix frees once; STOCK leaks it. *)
Theorem concrete_overput :
  guardedFrees 2 5 = true /\ floorFrees 2 5 = true /\ stockFrees 2 5 = false.
Proof. repeat split; reflexivity. Qed.

(* Tessera Property 2 / pgcl #143 task #8 — REFCOUNT CORRECTIVE FLOOR (r14reffloor, data-side face).
   Coq mirror of proof/Tessera/RefFloor.lean and property2/cbmc/ref_floor.c.

   r13refgate showed r12fix (mapcount corrective floor -> honest folio_mapcount) collapsed the
   code-page free-while-mapped; the residual is the REFCOUNT over-drop still freeing DATA folios
   while referenced (env/argv reuse + Bad rss type-swap).  SYMMETRIC fix: since folio_mapcount is
   now honest, floor the refcount put at mc (never below the refs the live mappings hold), so a
   referenced folio keeps rc >= mc >= 1 and is never freed. *)

Require Import Arith Lia.

Definition putFloor0 (rc k : nat) : nat := if k <=? rc then rc - k else 0.
Definition putFloorMc (rc mc k : nat) : nat := Nat.max (if k <=? rc then rc - k else 0) mc.

(* INVARIANT MAINTAINED: the corrective put keeps rc >= mc (refcount covers the mappings). *)
Theorem putFloorMc_ge_mc rc mc k : mc <= putFloorMc rc mc k.
Proof. unfold putFloorMc. apply Nat.le_max_r. Qed.

(* NO FREE WHILE MAPPED: rc reaches 0 ONLY when mc = 0 (unmapped). *)
Theorem putFloorMc_free_only_unmapped rc mc k : putFloorMc rc mc k = 0 -> mc = 0.
Proof. intro H. pose proof (putFloorMc_ge_mc rc mc k). lia. Qed.

(* THE BUG (stock 0-floor): a put k >= rc drives rc to 0 -- freeing a still-mapped folio (mc>0). *)
Theorem putFloor0_frees_mapped rc k : rc <= k -> putFloor0 rc k = 0.
Proof.
  intro H. unfold putFloor0. destruct (k <=? rc) eqn:E.
  - apply Nat.leb_le in E. lia.
  - reflexivity.
Qed.

(* ZERO BLAST RADIUS: when the put doesn't over-drop the mappings the corrective floor = stock. *)
Theorem putFloorMc_eq_when_room rc mc k :
  mc <= (if k <=? rc then rc - k else 0) ->
  putFloorMc rc mc k = (if k <=? rc then rc - k else 0).
Proof. intro H. unfold putFloorMc. apply Nat.max_l. exact H. Qed.

(* ---- r16owefloor: also refuse to free a GATHER-OWED folio (the reincarnation face) ----
   page_owner PROVED the residual double-free is a gather-owed folio over-dropped to 0 while
   UNMAPPED (mc=0, so putFloorMc lets it reach 0), freed, reincarnated by __vmalloc, stale-freed.
   Extend the floor to also hold >= 1 while owed. *)
Definition putFloorOwed (rc mc k : nat) (owed : bool) : nat :=
  Nat.max (putFloorMc rc mc k) (if owed then 1 else 0).

(* THE r16 RESULT: a gather-owed folio is NEVER freed by the over-drop (refcount >= 1). *)
Theorem putFloorOwed_owed_not_freed rc mc k : 1 <= putFloorOwed rc mc k true.
Proof. unfold putFloorOwed. change (if true then 1 else 0) with 1. apply Nat.le_max_r. Qed.

(* NO REINCARNATION: an owed folio's refcount never reaches 0. *)
Theorem owed_never_freed rc mc k : putFloorOwed rc mc k true = 0 -> False.
Proof. intro H. pose proof (putFloorOwed_owed_not_freed rc mc k). lia. Qed.

(* ZERO BLAST RADIUS: not owed => identical to the r14 mapcount floor. *)
Theorem putFloorOwed_eq_when_not_owed rc mc k :
  putFloorOwed rc mc k false = putFloorMc rc mc k.
Proof. unfold putFloorOwed. change (if false then 1 else 0) with 0. apply Nat.max_l. apply Nat.le_0_l. Qed.

(* The owe floor never DROPS the mapcount floor (still >= mc). *)
Theorem putFloorOwed_ge_mc rc mc k owed : mc <= putFloorOwed rc mc k owed.
Proof.
  unfold putFloorOwed. pose proof (putFloorMc_ge_mc rc mc k).
  pose proof (Nat.le_max_l (putFloorMc rc mc k) (if owed then 1 else 0)). lia.
Qed.

(* FULL CHAIN: r12fix (present<=mc) + r14 (mc<=rc) => present<=rc => free (rc=0) only when
   present=0.  Both the count that lies (mapcount) and the count that frees (refcount) floor at the
   present mappings. *)
Theorem no_free_while_present rc mc present :
  present <= mc -> mc <= rc -> rc = 0 -> present = 0.
Proof. lia. Qed.

(* Concrete: a folio mapped by 3 (mc=3), a bogus over-put of 5.  Stock frees it; the fix holds at 3. *)
Theorem concrete : putFloor0 3 5 = 0 /\ putFloorMc 3 3 5 = 3.
Proof. unfold putFloor0, putFloorMc. simpl. split; reflexivity. Qed.

(* ---- r19: the gather defers only the refs for the mappings it ACTUALLY removed ----
   r18 floored the mapcount removal to `own` edges but left the refcount deferral at the batch size
   nr >= own; at discharge it dropped nr refs on a folio whose refcount was own+other (OTHER owners
   hold `other`), over-dropping by nr-own into `other` -> data page freed-while-referenced (the
   OVERPUT deficit -> renderer SIGSEGV).  Defer exactly `own`. *)

Definition deferDrop (rc own : nat) : nat := rc - own.

(* NO OVER-DROP: deferring `own` from own+other leaves exactly the other owners' refs. *)
Theorem deferDrop_keeps_others own other :
  deferDrop (own + other) own = other.
Proof. unfold deferDrop. lia. Qed.

(* THE BUG (stock nr-defer): deferring nr>own drops below the other owners' refs. *)
Theorem stock_overdrops own other nr :
  own < nr -> 0 < other -> (own + other) - nr < other.
Proof. lia. Qed.

(* LOCKSTEP: own<=nr (floored edge count), so the refcount deferral never exceeds the mapcount removal. *)
Theorem deferDrop_ge_stock rc own nr :
  own <= nr -> rc - nr <= deferDrop rc own.
Proof. unfold deferDrop. lia. Qed.

(* FULL SYMMETRIC CLOSURE: while other owners hold a ref, the floored deferral keeps refcount > 0. *)
Theorem defer_no_free_while_referenced own other :
  0 < other -> 0 < deferDrop (own + other) own.
Proof. unfold deferDrop. lia. Qed.

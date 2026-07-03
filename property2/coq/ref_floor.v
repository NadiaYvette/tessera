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

(* FULL CHAIN: r12fix (present<=mc) + r14 (mc<=rc) => present<=rc => free (rc=0) only when
   present=0.  Both the count that lies (mapcount) and the count that frees (refcount) floor at the
   present mappings. *)
Theorem no_free_while_present rc mc present :
  present <= mc -> mc <= rc -> rc = 0 -> present = 0.
Proof. lia. Qed.

(* Concrete: a folio mapped by 3 (mc=3), a bogus over-put of 5.  Stock frees it; the fix holds at 3. *)
Theorem concrete : putFloor0 3 5 = 0 /\ putFloorMc 3 3 5 = 3.
Proof. unfold putFloor0, putFloorMc. simpl. split; reflexivity. Qed.

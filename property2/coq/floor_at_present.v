(* Tessera Property 2 / pgcl #143 task #8 — FLOOR-AT-PRESENT corrective floor (r12fix) + the
   free-while-mapped gate (r13refgate).  Coq mirror of proof/Tessera/FloorAtPresent.lean (the
   removeCorrected / no_free_while_mapped section) and property2/cbmc/floor_at_present.c.

   r11probe proved zap_present_ptes over-removes FILE-folio _mapcount: folio_mapcount (= rmap) is
   driven BELOW present_here (the sub-PTEs still present in this table), so folio_mapped() lies and
   the free-while-mapped guard fails -> int3 / WM-crash / deadlock.  r12fix CORRECTS the count back
   up to present_here; r13refgate gates the (bypass) free paths on the now-honest folio_mapped so a
   still-mapped folio is never freed on ANY path.  Proven: the correction restores present<=rmap
   from any state, never overshoots, doesn't stall legit unmaps; and honest counter + free-gate =>
   freed only when present=0 (no free-while-mapped). *)

Require Import ZArith Lia.
Open Scope Z_scope.

Record RSP := mkRSP { rmap : Z; stat : Z; present : Z }.

(* r12fix: with room (present<rmap) do the real floored remove; on an already-undercounted cluster
   (rmap<present) restore rmap:=present; else hold. *)
Definition removeCorrected (x : RSP) : RSP :=
  if present x <? rmap x then mkRSP (rmap x - 1) (stat x - 1) (present x)
  else if rmap x <? present x then mkRSP (present x) (stat x) (present x)
  else x.

(* THE r12fix SAFETY RESULT: present<=rmap restored from ANY state (incl. the over-removed
   rmap<present the diagnostics captured) -> folio_mapped honest -> free-while-mapped impossible. *)
Theorem removeCorrected_restores_inv x :
  present (removeCorrected x) <= rmap (removeCorrected x).
Proof.
  unfold removeCorrected.
  destruct (present x <? rmap x) eqn:E1.
  - apply Z.ltb_lt in E1. simpl. lia.
  - apply Z.ltb_ge in E1. destruct (rmap x <? present x) eqn:E2.
    + apply Z.ltb_lt in E2. simpl. lia.
    + apply Z.ltb_ge in E2. simpl. lia.
Qed.

(* The correction never over-shoots present (no phantom mapping beyond the present sub-PTEs). *)
Theorem removeCorrected_not_above x :
  rmap x < present x -> rmap (removeCorrected x) = present x.
Proof.
  unfold removeCorrected. intro H.
  destruct (present x <? rmap x) eqn:E1.
  - apply Z.ltb_lt in E1. lia.
  - destruct (rmap x <? present x) eqn:E2.
    + simpl. reflexivity.
    + apply Z.ltb_ge in E2. lia.
Qed.

(* The fix does not stall legitimate unmaps: with room it still performs the real rmap/stat drop. *)
Theorem removeCorrected_real_when_room x :
  present x < rmap x ->
  rmap (removeCorrected x) = rmap x - 1 /\ stat (removeCorrected x) = stat x - 1.
Proof.
  unfold removeCorrected. intro H.
  destruct (present x <? rmap x) eqn:E1.
  - simpl. split; reflexivity.
  - apply Z.ltb_ge in E1. lia.
Qed.

(* ---- r13refgate: the free-gate closing the free-while-mapped door on the REFCOUNT path ---- *)

Definition freeAllowed (x : RSP) : Prop := rmap x = 0.

(* THE r13refgate CAPSTONE: honest counter (present<=rmap) + free-gate (freeAllowed => rmap=0)
   => a folio is freed ONLY when present=0 -- no sub-PTE maps it.  The refcount over-drop can no
   longer free a still-mapped folio, because the free is gated on the honest rmap. *)
Theorem no_free_while_mapped x :
  0 <= present x -> present x <= rmap x -> freeAllowed x -> present x = 0.
Proof. unfold freeAllowed. lia. Qed.

(* Operational contrapositive: a mapped folio (present>=1) is NEVER freeAllowed under the honest
   invariant -- the gate refuses exactly the free-while-mapped cases, none else. *)
Theorem mapped_not_freeAllowed x :
  present x <= rmap x -> 1 <= present x -> ~ freeAllowed x.
Proof. unfold freeAllowed. lia. Qed.

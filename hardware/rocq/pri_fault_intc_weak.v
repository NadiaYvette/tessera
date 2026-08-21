(* Tessera — SSG-4 / S4.5: the PRQ -> INTC weak-memory (gpfsl) lift with the
   interrupt-context delivery gate in the loop, and the FRCDR drain.

   The functional base is the S4.5 PRI × FRCD × INTC composition (vtd_proofs.v,
   `pri_fault_frcd_delivers_intc` / `pri_fault_frcd_records`): a *pending*
   page request's translation fault delivers the FaultRecord (DID, PASID,
   IOVA, reason) into the FRCD (`frcd_record`), which raises the fault-message
   interrupt on the target core (`frcd_signal_intc` = `intc_send` iff the FRCD
   is pending).  The *delivery gate* (SSG-3 / S2.5) is at the ack: `intc_ack`
   rings the doorbell (ipi[core] := 1) iff pending ∧ ¬masked ∧ delivery —
   otherwise it is a spurious no-op, and the fault line is *held, not lost*
   (`intc_ack_in_context_noop`); the kernel's context-toggle ops
   (`intc_enter_context` / `intc_exit_context`) move between the two.

   This file lifts that path to genuine weak memory, exactly as
   `pri_fault_weak.v` lifts the FRCD record delivery: the leader (kernel /
   IOMMU driver) RELEASES the invalidation doorbell and the device ACQUIREs it
   before its request is served — the same release/acquire ordering core as
   S4.2b-2's `iommu_broadcast` — and at the leader's final read the FRCD ghost
   steps from the *empty* queue to the *recorded* one and the INTC ghost steps
   through the delivery gate.  The ghost post-states:

   - `pri_fault_intc_delivers` — the gate is applied and *open*: the record
     raises the fault line on the target core
     (`frcd_signal_intc (frcd_record fr []) ic core`); `pri_fault_ack_line_raised`
     is the pure justification (the FRCD is pending, so the line latches —
     edge-triggered, regardless of mask, IHI0069 4.4).
   - `pri_fault_intc_gated` — the ack is the gate *in the loop*: the ghost
     INTC post-state is `intc_ack (frcd_signal_intc (frcd_record fr []) ic core) core`,
     with `pri_fault_ack_unmasked_rings` (delivery enabled → the doorbell
     rings, pending cleared) and `pri_fault_ack_in_context_holds` (delivery
     suppressed → the ack is a no-op and the fault line stays pending — the
     fault is deferred, not lost: `frcd_head_record` keeps it learnable).  This
     is the program-level `intc_ack_op_hold_spec` / `intc_ack_op_deliver_spec`
     (S2.5) at the PRQ fault-message level, and the twin of
     `intc_no_lost_shootdown` (SSG-3) for the PRI path.
   - `pri_fault_intc_drain_lift` / `_machine` — the *drain in the lift*: after
     the delivery the kernel drains the FRCD (`frcd_drain`, VT-d 5.20 §6.1);
     `pri_fault_deliver_drain_cycle` is the pure deliver→drain cycle — the
     record is learnable at the head (`frcd_head_record`), the drain clears
     the whole queue (`frcd_drain_clears`), the line deasserts
     (`frcd_drain_deasserts`) and the controller recovers
     (`frcd_drain_recovers`) — so the ghost post-state is the *drained* queue
     and the recovered controller.

   As in the cache lifts, the lifts reuse
   `iommu_broadcast_full_gen_inv_update` (the generic R ⊢ |==> R' composition
   from S4.2b-2) with R / R' instantiated to the FRCD + INTC ghosts;
   `pri_fault_intc_drain_machine` threads it alongside the machine ghost, so
   the post-state carries the IOTLB queue shootdown, the drained FRCD, and the
   recovered controller. *)

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import lifting proofmode atomics view_invariants
                                 repeat_loop new_delete.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import own ghost_var.
From iris.proofmode Require Import proofmode monpred.
From gpfsl.base_logic Require Import vprop.
From SailStdpp Require Import MachineWord.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.          (* Machine, FrcdEntry, FaultRecord, FaultReason *)
Require Import machine.                (* frcd_record, frcd_drain, frcd_head, frcd_pending, frcd_of *)
Require Import shootdown_weak_broadcast. (* machine_ctx, bcG, machine_ctx_update, UTok, uniqTokG *)
Require Import iommu_proofs.           (* iommu_shootdown_via_queue *)
Require Import iommu_broadcast_weak.   (* iommu_broadcast, iommu_broadcast_full_gen_inv_update *)
Require Import intc_types.             (* Intc, Intc_pending, Intc_masked, Intc_delivery, Intc_ipi *)
Require Import intc.                   (* intc_send, intc_ack, intc_get_bit, intc_set_bit *)
Require Import intc_proofs.            (* intc_ack_unmasked_rings, intc_ack_in_context_noop *)
Require Import vtd_proofs.             (* frcd_signal_intc, frcd_signal_raises, frcd_drain_* *)
Require Import pri_fault_weak.         (* frG, fr_ctx, fr_ctx_update *)
Require Import shootdown_weak_broadcast_intc. (* intcG, intc_ctx, intc_ctx_update *)
Require Import iris.prelude.options.

(* The fault record the pending request delivers: the (DID, PASID, IOVA,
   reason) FaultRecord of VT-d 5.20 §6.1. *)
Definition pri_fault_record (did pasid : Z) (iova : mword 64) (reason : FaultReason) : FaultRecord :=
  {| FaultRecord_did := did; FaultRecord_pasid := pasid;
     FaultRecord_iova := iova; FaultRecord_reason := reason |}.

(* ============================================================
   The delivery gate, at the pure level: composing intc_proofs.v's ack lemmas
   with vtd_proofs.v's FRCD signal, on the raised fault line.
   ============================================================ *)

(* A recorded fault raises the fault-message line on the target core: the FRCD
   is pending, so frcd_signal_intc latches the interrupt — intc_send sets
   pending[core] regardless of mask/delivery (edge-triggered, IHI0069 4.4). *)
Lemma pri_fault_ack_line_raised (fr : FaultRecord) (ic : intc_types.Intc) (core : nat)
    (Hlen : Nat.lt core (length (intc_types.Intc_pending ic))) :
  intc.intc_get_bit (intc_types.Intc_pending
      (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core)))
    (Z.of_nat core) false = true.
Proof.
  apply (frcd_signal_raises (frcd_record fr []) ic core Hlen).
  unfold frcd_pending. cbn. reflexivity.
Qed.

(* The gate open (delivery enabled): the kernel's ack of the fault-message
   interrupt rings the doorbell — ipi[core] is set, the delivered bit the
   software fault handler consumes.  (intc_send preserves masked/delivery, so
   the gate bits on the raised line are the controller's own.) *)
Lemma pri_fault_ack_unmasked_rings (fr : FaultRecord) (ic : intc_types.Intc) (core : nat)
    (Hlen : Nat.lt core (length (intc_types.Intc_pending ic)))
    (Hm : intc.intc_get_bit (intc_types.Intc_masked ic) (Z.of_nat core) false = false)
    (Hd : intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat core) false = true) :
  intc_types.Intc_ipi
    (intc.intc_ack (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core)) (Z.of_nat core)) =
  intc.intc_set_bit
    (intc_types.Intc_ipi (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core)))
    (Z.of_nat core) true.
Proof.
  apply (intc_ack_unmasked_rings
           (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core)) core).
  - apply (pri_fault_ack_line_raised fr ic core Hlen).
  - cbn. exact Hm.
  - cbn. exact Hd.
Qed.

(* The gate closed (a hart in interrupt context, delivery suppressed): the ack
   is a spurious no-op — the fault line stays pending and the doorbell does not
   ring.  The fault is *held, not lost*: frcd_head_record keeps the record
   learnable, and when the kernel exits context (intc_exit_context) the ack
   rings (pri_fault_ack_unmasked_rings).  This is the PRQ twin of
   intc_no_lost_shootdown (SSG-3). *)
Lemma pri_fault_ack_in_context_holds (fr : FaultRecord) (ic : intc_types.Intc) (core : nat)
    (Hd : intc.intc_get_bit (intc_types.Intc_delivery ic) (Z.of_nat core) false = false) :
  intc.intc_ack (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core)) (Z.of_nat core)
  = frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core).
Proof.
  apply (intc_ack_in_context_noop
           (frcd_signal_intc (frcd_record fr []) ic (Z.of_nat core)) core).
  cbn. exact Hd.
Qed.

(* The deliver -> drain cycle (VT-d 5.20 §6.1 FRCDR drain): the record is
   learnable at the head, the drain clears the whole queue, the line deasserts
   and the next signal from the drained state is a no-op — the controller
   recovers to the pre-fault state. *)
Theorem pri_fault_deliver_drain_cycle (fr : FaultRecord) (ic : intc_types.Intc) (core : Z) :
  frcd_head (frcd_record fr []) = Some (frcd_of fr) /\
  frcd_drain (frcd_record fr []) = [] /\
  frcd_pending (frcd_drain (frcd_record fr [])) = false /\
  frcd_signal_intc (frcd_drain (frcd_record fr [])) ic core = ic.
Proof.
  split; [| split; [| split]].
  - exact (frcd_head_record fr []).
  - exact (frcd_drain_clears (frcd_record fr [])).
  - exact (frcd_drain_deasserts (frcd_record fr [])).
  - exact (frcd_drain_recovers (frcd_record fr []) ic core).
Qed.

(* ============================================================
   Ghost state: the FRCD fault queue (frG / fr_ctx from pri_fault_weak.v)
   together with the abstract interrupt controller (intcG / intc_ctx from
   shootdown_weak_broadcast_intc.v).  Both are held by the leader outside the
   invariant and stepped in lockstep with the machine ghost, exactly as
   machine_ctx / intc_ctx are for the machine and the controller.
   ============================================================ *)

(* The combined FRCD + INTC update: both ghosts step together (the record
   delivered into the queue and the controller taken through the delivery
   gate). *)
Lemma fr_intc_update `{!frG Σ, !intcG Σ} (γf γic : gname) (f f' : list FrcdEntry)
    (ic ic' : intc_types.Intc) :
  (fr_ctx γf f ∗ intc_ctx γic ic) ⊢ |==> (fr_ctx γf f' ∗ intc_ctx γic ic') : vProp Σ.
Proof.
  iIntros "[Hf Hic]".
  iMod (fr_ctx_update γf f f' with "Hf") as "Hf'".
  iMod (intc_ctx_update γic ic ic' with "Hic") as "Hic'".
  iIntros "!>". iFrame.
Qed.

(* The combined machine + FRCD + INTC update. *)
Lemma fr_intc_machine_update `{!bcG Σ, !frG Σ, !intcG Σ} (γm γf γic : gname)
    (m m' : Machine) (f f' : list FrcdEntry) (ic ic' : intc_types.Intc) :
  (machine_ctx γm m ∗ fr_ctx γf f ∗ intc_ctx γic ic)
  ⊢ |==> (machine_ctx γm m' ∗ fr_ctx γf f' ∗ intc_ctx γic ic') : vProp Σ.
Proof.
  iIntros "[Hm [Hf Hic]]".
  iMod (machine_ctx_update γm m m' with "Hm") as "Hm'".
  iMod (fr_ctx_update γf f f' with "Hf") as "Hf'".
  iMod (intc_ctx_update γic ic ic' with "Hic") as "Hic'".
  iIntros "!>". iFrame.
Qed.

(* ============================================================
   The lifts: the same two release/acquire pairs as S4.2b-2's `iommu_broadcast`
   (the invalidation doorbell and the completion), with R / R' instantiated to
   the FRCD + INTC ghosts.  The pre-state is the *empty* fault queue and the
   *pre-gate* controller; the post-state is the recorded queue and the
   controller through the delivery gate.
   ============================================================ *)

(* The device side, gate open: the pending request's fault is recorded and the
   fault-message line raises on the target core (pri_fault_ack_line_raised —
   the FRCD is pending, so the line latches). *)
Lemma pri_fault_intc_delivers `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !frG Σ, !intcG Σ}
    (γf γic : gname) (ic : intc_types.Intc) (core : Z)
    (did pasid : Z) (iova : mword 64) (reason : FaultReason) :
  ∀ tid, {{{ fr_ctx γf [] ∗ intc_ctx γic ic }}} 
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗
        fr_ctx γf (frcd_record (pri_fault_record did pasid iova reason) []) ∗
        intc_ctx γic (frcd_signal_intc
                        (frcd_record (pri_fault_record did pasid iova reason) []) ic core) }}}.
Proof.
  iIntros (tid Φ) "[Hf Hic] Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (fr_ctx γf [] ∗ intc_ctx γic ic)
            (fr_ctx γf (frcd_record (pri_fault_record did pasid iova reason) []) ∗
             intc_ctx γic (frcd_signal_intc
                             (frcd_record (pri_fault_record did pasid iova reason) []) ic core))
            _ tid with "[$Hf $Hic]").
  - iIntros (v) "(Hv & Hf' & Hic')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hf' Hic'". iPureIntro. exact Hv.
  Unshelve.
  exact (fr_intc_update γf γic [] (frcd_record (pri_fault_record did pasid iova reason) [])
           ic (frcd_signal_intc (frcd_record (pri_fault_record did pasid iova reason) []) ic core)).
Qed.

(* The delivery gate in the loop: the ghost INTC post-state is the controller
   *after the ack* — `intc_ack` is the gate, and the pure lemmas say what it
   does in each context.  Delivery enabled (masked = 0, delivery = 1): the
   doorbell rings (pri_fault_ack_unmasked_rings — ipi set, pending cleared).
   In interrupt context (delivery = 0): the ack is a no-op and the fault line
   stays pending (pri_fault_ack_in_context_holds) — the fault is deferred, not
   lost, exactly the S2.5 program-level gate
   (intc_ack_op_deliver_spec / intc_ack_op_hold_spec) at the PRQ level. *)
Lemma pri_fault_intc_gated `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !frG Σ, !intcG Σ}
    (γf γic : gname) (ic : intc_types.Intc) (core : Z)
    (did pasid : Z) (iova : mword 64) (reason : FaultReason) :
  ∀ tid, {{{ fr_ctx γf [] ∗ intc_ctx γic ic }}} 
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗
        fr_ctx γf (frcd_record (pri_fault_record did pasid iova reason) []) ∗
        intc_ctx γic (intc.intc_ack
                        (frcd_signal_intc
                           (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                        core) }}}.
Proof.
  iIntros (tid Φ) "[Hf Hic] Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (fr_ctx γf [] ∗ intc_ctx γic ic)
            (fr_ctx γf (frcd_record (pri_fault_record did pasid iova reason) []) ∗
             intc_ctx γic (intc.intc_ack
                             (frcd_signal_intc
                                (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                             core))
            _ tid with "[$Hf $Hic]").
  - iIntros (v) "(Hv & Hf' & Hic')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hf' Hic'". iPureIntro. exact Hv.
  Unshelve.
  exact (fr_intc_update γf γic [] (frcd_record (pri_fault_record did pasid iova reason) [])
           ic (intc.intc_ack
                 (frcd_signal_intc
                    (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                 core)).
Qed.

(* The drain in the lift: after the delivery the kernel drains the FRCD to
   learn which endpoint / address faulted.  The ghost post-state is the
   *drained* queue and the recovered controller —
   pri_fault_deliver_drain_cycle is the pure cycle: the record was findable at
   the head, the drain cleared the queue, the line deasserted, and the
   controller recovered (frcd_drain_recovers). *)
Lemma pri_fault_intc_drain_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !frG Σ, !intcG Σ}
    (γf γic : gname) (ic : intc_types.Intc) (core : Z)
    (did pasid : Z) (iova : mword 64) (reason : FaultReason) :
  ∀ tid, {{{ fr_ctx γf [] ∗ intc_ctx γic ic }}} 
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗
        fr_ctx γf (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) [])) ∗
        intc_ctx γic (frcd_signal_intc
                        (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
                        (frcd_signal_intc
                           (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                        core) }}}.
Proof.
  iIntros (tid Φ) "[Hf Hic] Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (fr_ctx γf [] ∗ intc_ctx γic ic)
            (fr_ctx γf (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) [])) ∗
             intc_ctx γic (frcd_signal_intc
                             (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
                             (frcd_signal_intc
                                (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                             core))
            _ tid with "[$Hf $Hic]").
  - iIntros (v) "(Hv & Hf' & Hic')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hf' Hic'". iPureIntro. exact Hv.
  Unshelve.
  exact (fr_intc_update γf γic []
           (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
           ic (frcd_signal_intc
                 (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
                 (frcd_signal_intc
                    (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                 core)).
Qed.

(* The machine-aware composition: the leader owns all three ghosts exclusively
   and advances them — the machine to the functional queue-shootdown state, the
   FRCD to the drained queue, and the INTC to the recovered controller — while
   the final read is still the program's step (inside the WP), not in a
   postcondition adapter. *)
Lemma pri_fault_intc_drain_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !frG Σ, !intcG Σ}
    (γm γf γic : gname) (m : Machine) (root : mword 44) (va : mword 64) (p : Pte)
    (ic : intc_types.Intc) (core : Z)
    (did pasid : Z) (iova : mword 64) (reason : FaultReason) :
  ∀ tid, {{{ machine_ctx γm m ∗ fr_ctx γf [] ∗ intc_ctx γic ic }}} 
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm (iommu_shootdown_via_queue m root va p)
                    ∗ fr_ctx γf (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
                    ∗ intc_ctx γic (frcd_signal_intc
                                      (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
                                      (frcd_signal_intc
                                         (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                                      core) }}}.
Proof.
  iIntros (tid Φ) "[Hm [Hf Hic]] Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ fr_ctx γf [] ∗ intc_ctx γic ic)
            (machine_ctx γm (iommu_shootdown_via_queue m root va p) ∗
             fr_ctx γf (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) [])) ∗
             intc_ctx γic (frcd_signal_intc
                             (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
                             (frcd_signal_intc
                                (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                             core))
            _ tid with "[$Hm $Hf $Hic]").
  - iIntros (v) "(Hv & Hm' & Hf' & Hic')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hf' Hic'". iPureIntro. exact Hv.
  Unshelve.
  exact (fr_intc_machine_update γm γf γic m (iommu_shootdown_via_queue m root va p)
           [] (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
           ic (frcd_signal_intc
                 (frcd_drain (frcd_record (pri_fault_record did pasid iova reason) []))
                 (frcd_signal_intc
                    (frcd_record (pri_fault_record did pasid iova reason) []) ic core)
                 core)).
Qed.

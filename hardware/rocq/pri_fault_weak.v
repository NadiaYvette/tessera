(* Tessera — SSG-4 / S4.5: the weak-memory (gpfsl) lift of the PRI fault
   delivery path.

   The functional base is the S4.5 PRI × FRCD × INTC composition (vtd_proofs.v,
   `pri_fault_frcd_delivers_intc`): a *pending* page request's translation
   fault delivers the FaultRecord (DID, PASID, IOVA, reason) into the FRCD
   (`frcd_record`), which raises the fault-message interrupt on the target
   core (`frcd_signal_intc`).  Once the kernel maps the page the request is
   resolved and the path is silent (no record, no line).

   This file lifts that delivery to genuine weak memory, exactly as
   `pasid_translate_weak.v` / `vtd_device_translate_weak.v` lift the cache
   translation loops: the leader (kernel / IOMMU driver) RELEASES the
   invalidation doorbell and the device ACQUIREs it before its request is
   served — the same release/acquire ordering core as S4.2b-2's
   `iommu_broadcast` — and at the leader's final read the FRCD ghost steps
   from the *empty* queue to the *recorded* one: the ghost post-state is
   exactly `frcd_record fr []` for the delivered record `fr`, justified at
   the pure level by `pri_fault_frcd_records` (the record is produced iff the
   request is pending, is findable at the head, and raises the line).  The
   ghost `fr_ctx` is a fresh `ghost_var` over `list FrcdEntry` — the fault
   queue the kernel will drain (`frcd_drain`) to learn which endpoint
   faulted is itself part of the verified state.

   As in the cache lifts, the lift reuses
   `iommu_broadcast_full_gen_inv_update` (the generic R ⊢ |==> R' composition
   from S4.2b-2) with R / R' instantiated to the FRCD ghost;
   `pri_fault_fr_machine` threads it alongside the machine ghost, so the
   post-state carries both the IOTLB queue shootdown and the recorded fault.
   The resolved path is the identity lift (R = R' = the empty FRCD — a
   resolved request delivers no record, `pri_fault_frcd_resolved_silent`). *)

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
Require Import machine.                (* frcd_record *)
Require Import shootdown_weak_broadcast. (* machine_ctx, bcG, machine_ctx_update, UTok, uniqTokG *)
Require Import iommu_proofs.           (* iommu_shootdown_via_queue *)
Require Import iommu_broadcast_weak.   (* iommu_broadcast, iommu_broadcast_full_gen_inv_update *)
Require Import iris.prelude.options.

(* ============================================================
   Ghost state: the FRCD fault queue.  The machine ghost (bcG / machine_ctx)
   comes from shootdown_weak_broadcast; `fr_ctx` is a fresh ghost_var over the
   IOMMU's fault-record cache, stepped at the leader's final read from the
   empty queue (nothing recorded yet) to the queue with the delivered record.
   ============================================================ *)

Class frG Σ := FrG { fr_frcdG : ghost_varG Σ (list FrcdEntry); }.
Local Existing Instances fr_frcdG.
Definition frΣ : gFunctors := #[ghost_varΣ (list FrcdEntry)].
Global Instance subG_frΣ {Σ} : subG frΣ Σ → frG Σ.
Proof. solve_inG. Qed.

(* The FRCD ghost, embedded into gpfsl's vProp. *)
Definition fr_ctx `{!frG Σ} (γf : gname) (f : list FrcdEntry) : vProp Σ :=
  ⎡ ghost_var γf (DfracOwn 1) f ⎤.

#[global] Instance fr_ctx_objective `{!frG Σ} γf f : Objective (fr_ctx γf f).
Proof. rewrite /fr_ctx. apply _. Qed.

(* The leader owns the FRCD ghost exclusively, so it may step it to any
   value; faithfulness (the ghost always matches the constrained physical
   queue) is by construction of the proof, exactly as in S2.1's Honesty note
   and the S4.2b-2 machine corollary. *)
Lemma fr_ctx_update `{!frG Σ} (γf : gname) (f f' : list FrcdEntry) :
  fr_ctx γf f ⊢ |==> fr_ctx γf f' : vProp Σ.
Proof.
  rewrite /fr_ctx. iIntros "Hf".
  iMod (ghost_var_update f' γf f with "Hf") as "Hf'".
  iIntros "!>". by iFrame.
Qed.

(* ============================================================
   The lift: the same two release/acquire pairs as S4.2b-2's `iommu_broadcast`
   (the invalidation doorbell and the completion), with R / R' instantiated
   to the FRCD ghost.  The pre-state is the *empty* fault queue (the device's
   pending request is about to be served) and the post-state is the queue
   with the delivered fault record prepended — the fault-message path the
   kernel will drain.
   ============================================================ *)

Lemma pri_fault_fr_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !frG Σ}
    (γf : gname) (did pasid : Z) (iova : mword 64) (reason : FaultReason) :
  ∀ tid, {{{ fr_ctx γf [] }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ fr_ctx γf (frcd_record {| FaultRecord_did := did;
                                                    FaultRecord_pasid := pasid;
                                                    FaultRecord_iova := iova;
                                                    FaultRecord_reason := reason |} []) }}}.
Proof.
  iIntros (tid Φ) "Hf Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (fr_ctx γf [])
            (fr_ctx γf (frcd_record {| FaultRecord_did := did;
                                       FaultRecord_pasid := pasid;
                                       FaultRecord_iova := iova;
                                       FaultRecord_reason := reason |} [])) _ tid
            with "Hf").
  - iIntros (v) "(Hv & Hf')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hf'". iPureIntro. exact Hv.
  Unshelve.
  exact (fr_ctx_update γf []
           (frcd_record {| FaultRecord_did := did; FaultRecord_pasid := pasid;
                           FaultRecord_iova := iova; FaultRecord_reason := reason |} [])).
Qed.

(* The resolved path is silent: with the request resolved the kernel maps the
   page and no fault record is delivered, so the FRCD ghost stays empty — the
   identity update. *)
Lemma pri_fault_fr_silent_lift `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !frG Σ}
    (γf : gname) :
  ∀ tid, {{{ fr_ctx γf [] }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ fr_ctx γf [] }}}.
Proof.
  iIntros (tid Φ) "Hf Post".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (fr_ctx γf []) (fr_ctx γf []) _ tid
            with "Hf").
  - iIntros (v) "(Hv & Hf')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hf'". iPureIntro. exact Hv.
  Unshelve.
  exact (fr_ctx_update γf [] []).
Qed.

(* The combined update: both ghosts step together (the IOTLB queue shootdown
   and the FRCD fault record). *)
Lemma fr_machine_update `{!bcG Σ, !frG Σ} (γm γf : gname) (m m' : Machine)
    (f f' : list FrcdEntry) :
  (machine_ctx γm m ∗ fr_ctx γf f) ⊢ |==> (machine_ctx γm m' ∗ fr_ctx γf f') : vProp Σ.
Proof.
  iIntros "[Hm Hf]".
  iMod (machine_ctx_update γm m m' with "Hm") as "Hm'".
  iMod (fr_ctx_update γf f f' with "Hf") as "Hf'".
  iIntros "!>". iFrame.
Qed.

(* The machine-aware composition: the leader owns both ghosts exclusively and
   advances them — the machine to the functional queue-shootdown state and the
   FRCD to the queue with the delivered fault record — while the final read is
   still the program's step (inside the WP), not in a postcondition adapter. *)
Lemma pri_fault_fr_machine `{!noprolG Σ, !atomicG Σ, !shootdown_weak.uniqTokG Σ, !bcG Σ, !frG Σ}
    (γm γf : gname) (m : Machine) (root : mword 44) (va : mword 64) (p : Pte)
    (did pasid : Z) (iova : mword 64) (reason : FaultReason) :
  ∀ tid, {{{ machine_ctx γm m ∗ fr_ctx γf [] }}}
    iommu_broadcast @ tid; ⊤
  {{{ v, RET #v; ⌜v = 1⌝ ∗ machine_ctx γm (iommu_shootdown_via_queue m root va p)
                    ∗ fr_ctx γf (frcd_record {| FaultRecord_did := did;
                                                FaultRecord_pasid := pasid;
                                                FaultRecord_iova := iova;
                                                FaultRecord_reason := reason |} []) }}}.
Proof.
  iIntros (tid Φ) "Hm Post".
  iDestruct "Hm" as "[Hm Hf]".
  wp_apply (iommu_broadcast_full_gen_inv_update (Σ := Σ)
            (machine_ctx γm m ∗ fr_ctx γf [])
            (machine_ctx γm (iommu_shootdown_via_queue m root va p)
             ∗ fr_ctx γf (frcd_record {| FaultRecord_did := did;
                                         FaultRecord_pasid := pasid;
                                         FaultRecord_iova := iova;
                                         FaultRecord_reason := reason |} [])) _ tid
            with "[$Hm $Hf]").
  - iIntros (v) "(Hv & Hm' & Hf')". iDestruct "Hv" as %Hv. iApply ("Post" $! v).
    iFrame "Hm' Hf'". iPureIntro. exact Hv.
  Unshelve.
  exact (fr_machine_update γm γf m (iommu_shootdown_via_queue m root va p) []
           (frcd_record {| FaultRecord_did := did; FaultRecord_pasid := pasid;
                           FaultRecord_iova := iova; FaultRecord_reason := reason |} [])).
Qed.

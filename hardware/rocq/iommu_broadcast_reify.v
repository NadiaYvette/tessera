(* Tessera — S4.2b-2 (reification bridge): the composition's IOMMU drain ghost
   step is the MMIO command queue, and its effect is exactly the functional
   queue shootdown (S4.2b-1).

   The weak-memory program (`iommu_broadcast_full_gen_inv`) has the leader
   enqueue [Invalidate va; Wait] and ring the doorbell; the IOMMU acquire +
   drain + release the Invalidation-Wait completion; the leader acquire + read
   the drained result.  That program's *abstract* spec says the leader observes
   `1`.  This file is the *pure* bridge that gives the `1` its machine meaning:

       leader enqueue (MMIO `cmdq_enqueue`, doorbell = prod+1)
         -> IOMMU drain (`cmdq_drain`, the ghost step)
         -> `iommu_process_queue` (the functional FIFO drain, `cmdq_drain` is
            literally `iommu_process_queue` over the entry list)
         -> `iommu_shootdown_via_queue`'s IOTLB (S4.2b-1)
         -> `iommu_shootdown_via_queue_correct` (walk faults, no stale entry).

   So the program's "leader observes the drain" reifies to "the freed frame
   faults and no stale IOTLB entry survives".  This mirrors S2.4's
   `bc_machine_ipi_step` / S2.5's `bc_machine_ipi_step_via_intc`: the pure
   precondition the gpfsl program's ghost state must satisfy.

   See doc/iommu-shootdown-plan.md (S4.2b-2) and doc/system-state-goals.md
   (SSG-4). *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import machine_types.
Require Import machine.
Require Import machine_encoding. (* invalid_pte (test vector) *)
Require Import iommu_proofs.   (* iommu_shootdown_via_queue + _iotlb + _correct *)
Require Import cmdq_mmio.      (* cmdq_enqueue/cmdq_drain + invalidate_wait_spec *)
Import ListNotations.

(* ============================================================
   The MMIO enqueue of [Invalidate va; Wait] is the queue the functional
   shootdown drains.  The two descriptors are the same value in both files
   (`invalidation_cmd`/`wait_cmd` in cmdq_mmio.v, `invalidate_wait_queue` in
   iommu_proofs.v), so the doorbell ring (prod+1) is pure bookkeeping.
   ============================================================ *)

Definition iommu_broadcast_queue (va : mword 64) : Cmdq :=
  cmdq_enqueue (cmdq_enqueue cmdq_empty (invalidation_cmd va)) (wait_cmd va).

(* The IOMMU's drain ghost step: draining the doorbelled MMIO queue over the
   pre-IOTLB yields exactly `iommu_shootdown_via_queue`'s invalidated IOTLB. *)
Lemma iommu_drain_iotlb_reifies (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  cmdq_drain (iommu_broadcast_queue va) m.(Machine_iotlb)
  = Some (Machine_iotlb (iommu_shootdown_via_queue m root va p)).
Proof.
  unfold iommu_broadcast_queue.
  rewrite cmdq_drain_invalidate_wait_spec, iommu_shootdown_via_queue_iotlb.
  reflexivity.
Qed.

(* ============================================================
   The headline: the composition's drain (the doorbelled MMIO queue) produces
   the IOTLB the functional queue shootdown leaves, and that IOTLB — with the
   unmapped mem — satisfies `iommu_shootdown_via_queue_correct`: the device
   walk faults and no stale IOTLB entry survives.
   ============================================================ *)

Theorem iommu_broadcast_reifies_correct (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  p.(Pte_valid) = false ->
  exists iotlb',
    cmdq_drain (iommu_broadcast_queue va) m.(Machine_iotlb) = Some iotlb' /\
    iotlb' = Machine_iotlb (iommu_shootdown_via_queue m root va p) /\
    iommu_walk root (Machine_mem (iommu_shootdown_via_queue m root va p)) va = None /\
    Forall (fun e => vpn_of e.(IotlbEntry_iova) <> vpn_of va) iotlb'.
Proof.
  intros Hinv.
  exists (Machine_iotlb (iommu_shootdown_via_queue m root va p)).
  split; [apply iommu_drain_iotlb_reifies |].
  split; [reflexivity |].
  apply (iommu_shootdown_via_queue_correct m root va p Hinv).
Qed.

(* Executable vector: enqueue Invalidate 0 + Wait over a two-entry IOTLB and
   drain — the MMIO result is exactly the queue shootdown's survivor list
   (IOVA-0 dropped, IOVA-4096 kept). *)
Lemma test_vector_iommu_broadcast_reifies :
  cmdq_drain (iommu_broadcast_queue (mword_of_int 0 : mword 64)) [cmdq_dev0; cmdq_dev1]
  = Some (Machine_iotlb
            (iommu_shootdown_via_queue
               {| Machine_mem := []; Machine_cores := []; Machine_ram := []; Machine_ipi := [];
                  Machine_iotlb := [cmdq_dev0; cmdq_dev1]; Machine_devtlbs := [];
                  Machine_prireqs := []; Machine_ioqueue := []; Machine_stes := []; Machine_cds := [] |}
               (mword_of_int 0 : mword 44) (mword_of_int 0 : mword 64) invalid_pte)).
Proof. vm_compute. reflexivity. Qed.

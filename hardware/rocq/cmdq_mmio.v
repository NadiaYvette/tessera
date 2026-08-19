(* Tessera — SSG-4 / S4.2c: the command-queue MMIO interface (head/tail
   registers).

   S4.2b-1 added the functional command queue (`InvalidationCmd` +
   `Machine_ioqueue` + `iommu_process_queue`, a plain FIFO list).  The real
   hardware interface is a *ring buffer* the software and the IOMMU drive
   through two MMIO registers:

     - `prod` (CMD_PROD / AMD-Vi command-buffer head pointer): software writes
       descriptors into the buffer then advances this — the doorbell.
     - `cons` (CMD_CONS / AMD-Vi tail pointer): the IOMMU advances this as it
       drains descriptors.

   This file models that MMIO state as a `Cmdq` (entries + prod + cons), the
   software's `cmdq_enqueue` (append + advance prod) and the IOMMU's
   `cmdq_drain` (consume FIFO, apply each `IotlbInvalidate`, complete at the
   `InvalidationWait`).  The circular *wrap* (prod/cons modulo the buffer
   depth) is a later increment; here the buffer is linear, which is the SMMU
   CMDQ / AMD-Vi command buffer restricted to the non-wrapping case.

   The headline is `cmdq_drain_refines_iommu_process_queue`: the MMIO drain is
   exactly the functional `iommu_process_queue` on the entry list — the head/
   tail registers are pure bookkeeping, so the weak-memory lift (S4.2b-2) can
   reason about the MMIO doorbell and inherit S4.2b-1's functional drain.

   See doc/iommu-shootdown-plan.md (S4.2b) and doc/system-state-goals.md. *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import machine_types.
Require Import machine.
From Stdlib Require Import ZArith.
Import ListNotations.

(* The command queue's MMIO state: the (linear, non-wrapping) descriptor ring
   plus the software's doorbell (prod) and the IOMMU's drain pointer (cons). *)
Record Cmdq := { Cmdq_entries : list InvalidationCmd; Cmdq_prod : Z; Cmdq_cons : Z }.

Definition cmdq_empty : Cmdq := {| Cmdq_entries := []; Cmdq_prod := 0; Cmdq_cons := 0 |}.

Definition invalidation_cmd (va : mword 64) : InvalidationCmd :=
  {| InvalidationCmd_is_wait := false; InvalidationCmd_va := va |}.
Definition wait_cmd (va : mword 64) : InvalidationCmd :=
  {| InvalidationCmd_is_wait := true; InvalidationCmd_va := va |}.

(* Software writes a descriptor then rings the doorbell (advances prod). *)
Definition cmdq_enqueue (q : Cmdq) (cmd : InvalidationCmd) : Cmdq :=
  {| Cmdq_entries := q.(Cmdq_entries) ++ [cmd];
     Cmdq_prod := q.(Cmdq_prod) + 1;
     Cmdq_cons := q.(Cmdq_cons) |}.

(* The IOMMU consumes one descriptor (advancing cons); an empty queue returns
   None (nothing to drain). *)
Definition cmdq_consume (q : Cmdq) : option InvalidationCmd * Cmdq :=
  match q.(Cmdq_entries) with
  | [] => (None, q)
  | c :: rest =>
      (Some c, {| Cmdq_entries := rest; Cmdq_prod := q.(Cmdq_prod); Cmdq_cons := q.(Cmdq_cons) + 1 |})
  end.

(* The IOMMU drains: consume FIFO, applying each IotlbInvalidate to the IOTLB,
   completing (Some iotlb) at the Invalidation-Wait; a queue with no wait
   drains to None (no completion).  The recursion is over the entry list
   (structurally), so the record is just the MMIO bookkeeping. *)
Fixpoint cmdq_drain_entries (entries : list InvalidationCmd) (iotlb : list IotlbEntry)
  : option (list IotlbEntry) :=
  match entries with
  | [] => None
  | c :: rest =>
      if c.(InvalidationCmd_is_wait) then Some iotlb
      else cmdq_drain_entries rest (iotlb_invalidate iotlb c.(InvalidationCmd_va))
  end.

Definition cmdq_drain (q : Cmdq) (iotlb : list IotlbEntry) : option (list IotlbEntry) :=
  cmdq_drain_entries q.(Cmdq_entries) iotlb.

(* ============================================================
   The MMIO drain realizes the functional iommu_process_queue.
   ============================================================ *)

Lemma cmdq_drain_refines_iommu_process_queue (entries : list InvalidationCmd)
    (prod cons : Z) (iotlb : list IotlbEntry) :
  cmdq_drain {| Cmdq_entries := entries; Cmdq_prod := prod; Cmdq_cons := cons |} iotlb
  = iommu_process_queue entries iotlb.
Proof.
  cbn. revert iotlb.
  induction entries as [| c rest IH]; intros iotlb; cbn.
  - reflexivity.
  - destruct c.(InvalidationCmd_is_wait); [reflexivity |].
    apply (IH (iotlb_invalidate iotlb c.(InvalidationCmd_va))).
Qed.

(* Software enqueues [Invalidate va; Wait] and rings the doorbell; the IOMMU
   drains to the Invalidation-Wait, completing with the invalidated IOTLB. *)
Lemma cmdq_drain_invalidate_wait_spec (iotlb : list IotlbEntry) (va : mword 64) :
  cmdq_drain (cmdq_enqueue (cmdq_enqueue cmdq_empty (invalidation_cmd va)) (wait_cmd va)) iotlb
  = Some (iotlb_invalidate iotlb va).
Proof. cbn. reflexivity. Qed.

(* Executable vector: enqueue Invalidate 0 + Wait over a two-entry IOTLB, drain
   drops the IOVA-0 entry and completes with the survivor. *)
Definition cmdq_dev0 : IotlbEntry :=
  {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 0 : mword 64);
     IotlbEntry_pa := (mword_of_int 0 : mword 56); IotlbEntry_perm := ReadWrite |}.
Definition cmdq_dev1 : IotlbEntry :=
  {| IotlbEntry_did := 0; IotlbEntry_pasid := 0; IotlbEntry_iova := (mword_of_int 4096 : mword 64);
     IotlbEntry_pa := (mword_of_int 4096 : mword 56); IotlbEntry_perm := ReadWrite |}.

Lemma test_vector_cmdq_mmio_drain :
  cmdq_drain (cmdq_enqueue (cmdq_enqueue cmdq_empty (invalidation_cmd (mword_of_int 0 : mword 64)))
                          (wait_cmd (mword_of_int 0 : mword 64)))
             [cmdq_dev0; cmdq_dev1]
  = Some [cmdq_dev1].
Proof. vm_compute. reflexivity. Qed.

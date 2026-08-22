(* Tessera — the disk device (SSG-8): correctness proofs.
   All theorems axiom-free. *)

From Stdlib Require Import Bool ZArith.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import disk_types.
Require Import disk_ops.

(* Default state: no pending commands or completions *)
Lemma disk_default_cmd_not_pending :
  cmd_pending disk_default = false.
Proof. reflexivity. Qed.

Lemma disk_default_cmp_not_pending :
  cmp_pending disk_default = false.
Proof. reflexivity. Qed.

(* Configure rings: set ring_len to 32, head=0, tail=0 → still no pending *)
Definition configured_disk : DiskRegs :=
  {| DiskRegs_cmd_ring_base := mword_of_int 0;
     DiskRegs_cmd_ring_len := mword_of_int 32;
     DiskRegs_cmd_head := mword_of_int 0;
     DiskRegs_cmd_tail := mword_of_int 0;
     DiskRegs_cmp_ring_base := mword_of_int 0;
     DiskRegs_cmp_ring_len := mword_of_int 32;
     DiskRegs_cmp_head := mword_of_int 0;
     DiskRegs_cmp_tail := mword_of_int 0;
     DiskRegs_ctrl := mword_of_int 0;
     DiskRegs_status := mword_of_int 0;
     DiskRegs_irq_status := mword_of_int 0 |}.

Lemma configured_cmd_not_pending :
  cmd_pending configured_disk = false.
Proof. reflexivity. Qed.

(* Submit: advance cmd_tail, head stays → becomes pending *)
Definition after_cmd_submit : DiskRegs := cmd_submit configured_disk.

Lemma cmd_submit_creates_pending :
  cmd_pending after_cmd_submit = true.
Proof. reflexivity. Qed.

(* Complete: advance cmp_tail → becomes pending *)
Definition after_cmp_complete : DiskRegs := cmp_complete configured_disk.

Lemma cmp_complete_creates_pending :
  cmp_pending after_cmp_complete = true.
Proof. reflexivity. Qed.

(* Submit preserves ring_base *)
Lemma cmd_submit_preserves_ring_base :
  after_cmd_submit.(DiskRegs_cmd_ring_base) = configured_disk.(DiskRegs_cmd_ring_base).
Proof. reflexivity. Qed.

(* Complete preserves cmd registers *)
Lemma cmp_complete_preserves_cmd_head :
  after_cmp_complete.(DiskRegs_cmd_head) = configured_disk.(DiskRegs_cmd_head).
Proof. reflexivity. Qed.

(* Command opcode checks *)
Lemma is_read_read :
  is_read (Build_DiskCmd (mword_of_int 0) (mword_of_int 0) (mword_of_int 0x20) (mword_of_int 0) (mword_of_int 0)) = true.
Proof. reflexivity. Qed.

Lemma is_write_write :
  is_write (Build_DiskCmd (mword_of_int 0) (mword_of_int 0) (mword_of_int 0x28) (mword_of_int 0) (mword_of_int 0)) = true.
Proof. reflexivity. Qed.

Lemma is_flush_flush :
  is_flush (Build_DiskCmd (mword_of_int 0) (mword_of_int 0) (mword_of_int 0x35) (mword_of_int 0) (mword_of_int 0)) = true.
Proof. reflexivity. Qed.

(* Default command has zero LBA and length *)
Lemma disk_cmd_zero_lba :
  (Build_DiskCmd (mword_of_int 0) (mword_of_int 0) (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)).(DiskCmd_lba) = mword_of_int 0.
Proof. reflexivity. Qed.

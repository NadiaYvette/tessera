(* Tessera — the disk device (SSG-8): command/completion ring operations.
   All functions pure. *)

From Stdlib Require Import Bool ZArith List.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import disk_types.

(* Default NIC: rings empty, head=tail=0 *)
Definition disk_default : DiskRegs :=
  {| DiskRegs_cmd_ring_base := mword_of_int 0;
     DiskRegs_cmd_ring_len := mword_of_int 0;
     DiskRegs_cmd_head := mword_of_int 0;
     DiskRegs_cmd_tail := mword_of_int 0;
     DiskRegs_cmp_ring_base := mword_of_int 0;
     DiskRegs_cmp_ring_len := mword_of_int 0;
     DiskRegs_cmp_head := mword_of_int 0;
     DiskRegs_cmp_tail := mword_of_int 0;
     DiskRegs_ctrl := mword_of_int 0;
     DiskRegs_status := mword_of_int 0;
     DiskRegs_irq_status := mword_of_int 0 |}.

(* Command ring has pending commands when head != tail *)
Definition cmd_pending (d : DiskRegs) : bool :=
  neq_vec d.(DiskRegs_cmd_head) d.(DiskRegs_cmd_tail).

(* Completion ring has completed commands when head != tail *)
Definition cmp_pending (d : DiskRegs) : bool :=
  neq_vec d.(DiskRegs_cmp_head) d.(DiskRegs_cmp_tail).

(* Submit a command: advance cmd_tail (hardware picks up) *)
Definition cmd_submit (d : DiskRegs) : DiskRegs :=
  {| DiskRegs_cmd_ring_base := d.(DiskRegs_cmd_ring_base);
     DiskRegs_cmd_ring_len := d.(DiskRegs_cmd_ring_len);
     DiskRegs_cmd_head := d.(DiskRegs_cmd_head);
     DiskRegs_cmd_tail := mword_of_int (Z_of_N (mword_to_N d.(DiskRegs_cmd_tail)) + 1 mod
                          Z_of_N (mword_to_N d.(DiskRegs_cmd_ring_len)));
     DiskRegs_cmp_ring_base := d.(DiskRegs_cmp_ring_base);
     DiskRegs_cmp_ring_len := d.(DiskRegs_cmp_ring_len);
     DiskRegs_cmp_head := d.(DiskRegs_cmp_head);
     DiskRegs_cmp_tail := d.(DiskRegs_cmp_tail);
     DiskRegs_ctrl := d.(DiskRegs_ctrl);
     DiskRegs_status := d.(DiskRegs_status);
     DiskRegs_irq_status := d.(DiskRegs_irq_status) |}.

(* Complete a command: advance cmp_tail (driver acknowledges) *)
Definition cmp_complete (d : DiskRegs) : DiskRegs :=
  {| DiskRegs_cmd_ring_base := d.(DiskRegs_cmd_ring_base);
     DiskRegs_cmd_ring_len := d.(DiskRegs_cmd_ring_len);
     DiskRegs_cmd_head := d.(DiskRegs_cmd_head);
     DiskRegs_cmd_tail := d.(DiskRegs_cmd_tail);
     DiskRegs_cmp_ring_base := d.(DiskRegs_cmp_ring_base);
     DiskRegs_cmp_ring_len := d.(DiskRegs_cmp_ring_len);
     DiskRegs_cmp_head := d.(DiskRegs_cmp_head);
     DiskRegs_cmp_tail := mword_of_int (Z_of_N (mword_to_N d.(DiskRegs_cmp_tail)) + 1 mod
                          Z_of_N (mword_to_N d.(DiskRegs_cmp_ring_len)));
     DiskRegs_ctrl := d.(DiskRegs_ctrl);
     DiskRegs_status := d.(DiskRegs_status);
     DiskRegs_irq_status := d.(DiskRegs_irq_status) |}.

(* Flush command: opcode = 0x35 *)
Definition is_flush (cmd : DiskCmd) : bool :=
  eq_vec cmd.(DiskCmd_opcode) (mword_of_int 0x35).

(* Read command: opcode = 0x20 *)
Definition is_read (cmd : DiskCmd) : bool :=
  eq_vec cmd.(DiskCmd_opcode) (mword_of_int 0x20).

(* Write command: opcode = 0x28 *)
Definition is_write (cmd : DiskCmd) : bool :=
  eq_vec cmd.(DiskCmd_opcode) (mword_of_int 0x28).

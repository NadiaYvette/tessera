(* Tessera — the UART console device (SSG-6): 8250/16550 register set.

   uart_types.v (generated from uart.sail) provides the UartRegs record.
   This file hand-writes the operations.  All functions pure. *)

From Stdlib Require Import Bool ZArith List.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import uart_types.

(* Default UART: all registers zero, tx and rx ready. *)
Definition uart_default : UartRegs :=
  {| UartRegs_thr := mword_of_int 0;
     UartRegs_rbr := mword_of_int 0;
     UartRegs_ier := mword_of_int 0;
     UartRegs_iir := mword_of_int 0;
     UartRegs_fcr := mword_of_int 0;
     UartRegs_lcr := mword_of_int 0;
     UartRegs_mcr := mword_of_int 0;
     UartRegs_lsr := mword_of_int 0;
     UartRegs_msr := mword_of_int 0;
     UartRegs_scr := mword_of_int 0;
     UartRegs_dll := mword_of_int 0;
     UartRegs_dlh := mword_of_int 0;
     UartRegs_tx_ready := true;
     UartRegs_rx_ready := false |}.

(* Write to THR: store character and clear tx_ready. *)
Definition uart_write_thr (u : UartRegs) (ch : mword 8) : UartRegs :=
  {| UartRegs_thr := ch;
     UartRegs_rbr := u.(UartRegs_rbr);
     UartRegs_ier := u.(UartRegs_ier);
     UartRegs_iir := u.(UartRegs_iir);
     UartRegs_fcr := u.(UartRegs_fcr);
     UartRegs_lcr := u.(UartRegs_lcr);
     UartRegs_mcr := u.(UartRegs_mcr);
     UartRegs_lsr := u.(UartRegs_lsr);
     UartRegs_msr := u.(UartRegs_msr);
     UartRegs_scr := u.(UartRegs_scr);
     UartRegs_dll := u.(UartRegs_dll);
     UartRegs_dlh := u.(UartRegs_dlh);
     UartRegs_tx_ready := false;
     UartRegs_rx_ready := u.(UartRegs_rx_ready) |}.

(* Tx complete: transfer THR to RBR (loopback) and set tx_ready. *)
Definition uart_tx_complete (u : UartRegs) : UartRegs :=
  {| UartRegs_thr := mword_of_int 0;
     UartRegs_rbr := u.(UartRegs_thr);
     UartRegs_ier := u.(UartRegs_ier);
     UartRegs_iir := u.(UartRegs_iir);
     UartRegs_fcr := u.(UartRegs_fcr);
     UartRegs_lcr := u.(UartRegs_lcr);
     UartRegs_mcr := u.(UartRegs_mcr);
     UartRegs_lsr := u.(UartRegs_lsr);
     UartRegs_msr := u.(UartRegs_msr);
     UartRegs_scr := u.(UartRegs_scr);
     UartRegs_dll := u.(UartRegs_dll);
     UartRegs_dlh := u.(UartRegs_dlh);
     UartRegs_tx_ready := true;
     UartRegs_rx_ready := true |}.

(* Read RBR: returns character and clears rx_ready. *)
Definition uart_read_rbr (u : UartRegs) : mword 8 * UartRegs :=
  (u.(UartRegs_rbr),
   {| UartRegs_thr := u.(UartRegs_thr);
      UartRegs_rbr := mword_of_int 0;
      UartRegs_ier := u.(UartRegs_ier);
      UartRegs_iir := u.(UartRegs_iir);
      UartRegs_fcr := u.(UartRegs_fcr);
      UartRegs_lcr := u.(UartRegs_lcr);
      UartRegs_mcr := u.(UartRegs_mcr);
      UartRegs_lsr := u.(UartRegs_lsr);
      UartRegs_msr := u.(UartRegs_msr);
      UartRegs_scr := u.(UartRegs_scr);
      UartRegs_dll := u.(UartRegs_dll);
      UartRegs_dlh := u.(UartRegs_dlh);
      UartRegs_tx_ready := u.(UartRegs_tx_ready);
      UartRegs_rx_ready := false |}).

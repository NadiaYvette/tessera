(* Tessera — the network device (SSG-7): DMA descriptor ring operations.
   All functions pure. *)

From Stdlib Require Import Bool ZArith List.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import net_types.

(* Default NIC: rings empty, head=tail=0 *)
Definition net_default : NetRegs :=
  {| NetRegs_tx_ring_base := mword_of_int 0;
     NetRegs_tx_ring_len := mword_of_int 0;
     NetRegs_tx_head := mword_of_int 0;
     NetRegs_tx_tail := mword_of_int 0;
     NetRegs_rx_ring_base := mword_of_int 0;
     NetRegs_rx_ring_len := mword_of_int 0;
     NetRegs_rx_head := mword_of_int 0;
     NetRegs_rx_tail := mword_of_int 0;
     NetRegs_ctrl := mword_of_int 0;
     NetRegs_status := mword_of_int 0;
     NetRegs_irq_status := mword_of_int 0 |}.

(* TX ring has pending descriptors when head != tail *)
Definition tx_pending (n : NetRegs) : bool :=
  neq_vec n.(NetRegs_tx_head) n.(NetRegs_tx_tail).

(* RX ring has space when head != tail (simplified) *)
Definition rx_pending (n : NetRegs) : bool :=
  neq_vec n.(NetRegs_rx_head) n.(NetRegs_rx_tail).

(* Advance TX head after DMA transmit *)
Definition tx_advance_head (n : NetRegs) : NetRegs :=
  {| NetRegs_tx_ring_base := n.(NetRegs_tx_ring_base);
     NetRegs_tx_ring_len := n.(NetRegs_tx_ring_len);
     NetRegs_tx_head := mword_of_int (Z_of_N (mword_to_N n.(NetRegs_tx_head)) + 1 mod
                         Z_of_N (mword_to_N n.(NetRegs_tx_ring_len)));
     NetRegs_tx_tail := n.(NetRegs_tx_tail);
     NetRegs_rx_ring_base := n.(NetRegs_rx_ring_base);
     NetRegs_rx_ring_len := n.(NetRegs_rx_ring_len);
     NetRegs_rx_head := n.(NetRegs_rx_head);
     NetRegs_rx_tail := n.(NetRegs_rx_tail);
     NetRegs_ctrl := n.(NetRegs_ctrl);
     NetRegs_status := n.(NetRegs_status);
     NetRegs_irq_status := n.(NetRegs_irq_status) |}.

(* Advance RX tail after DMA receive *)
Definition rx_advance_tail (n : NetRegs) : NetRegs :=
  {| NetRegs_tx_ring_base := n.(NetRegs_tx_ring_base);
     NetRegs_tx_ring_len := n.(NetRegs_tx_ring_len);
     NetRegs_tx_head := n.(NetRegs_tx_head);
     NetRegs_tx_tail := n.(NetRegs_tx_tail);
     NetRegs_rx_ring_base := n.(NetRegs_rx_ring_base);
     NetRegs_rx_ring_len := n.(NetRegs_rx_ring_len);
     NetRegs_rx_head := n.(NetRegs_rx_head);
     NetRegs_rx_tail := mword_of_int (Z_of_N (mword_to_N n.(NetRegs_rx_tail)) + 1 mod
                          Z_of_N (mword_to_N n.(NetRegs_rx_ring_len)));
     NetRegs_ctrl := n.(NetRegs_ctrl);
     NetRegs_status := n.(NetRegs_status);
     NetRegs_irq_status := n.(NetRegs_irq_status) |}.

(* Tessera — the network device (SSG-7): correctness proofs.
   All theorems axiom-free. *)

From Stdlib Require Import Bool ZArith.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import net_types.
Require Import net_ops.

(* Default state: no pending TX or RX *)
Lemma net_default_tx_not_pending :
  tx_pending net_default = false.
Proof. reflexivity. Qed.

Lemma net_default_rx_not_pending :
  rx_pending net_default = false.
Proof. reflexivity. Qed.

(* Configure ring: set ring_len to 8, head=0, tail=0 → still no pending *)
Definition configured_net : NetRegs :=
  {| NetRegs_tx_ring_base := mword_of_int 0;
     NetRegs_tx_ring_len := mword_of_int 8;
     NetRegs_tx_head := mword_of_int 0;
     NetRegs_tx_tail := mword_of_int 0;
     NetRegs_rx_ring_base := mword_of_int 0;
     NetRegs_rx_ring_len := mword_of_int 8;
     NetRegs_rx_head := mword_of_int 0;
     NetRegs_rx_tail := mword_of_int 0;
     NetRegs_ctrl := mword_of_int 0;
     NetRegs_status := mword_of_int 0;
     NetRegs_irq_status := mword_of_int 0 |}.

Lemma configured_not_pending :
  tx_pending configured_net = false.
Proof. reflexivity. Qed.

(* TX advance: head moves, tail stays → becomes pending *)
Definition after_tx_advance : NetRegs := tx_advance_head configured_net.

Lemma tx_advance_creates_pending :
  tx_pending after_tx_advance = true.
Proof. reflexivity. Qed.

(* RX advance: tail moves, head stays → becomes pending *)
Definition after_rx_advance : NetRegs := rx_advance_tail configured_net.

Lemma rx_advance_creates_pending :
  rx_pending after_rx_advance = true.
Proof. reflexivity. Qed.

(* TX advance preserves ring base *)
Lemma tx_advance_preserves_ring_base :
  after_tx_advance.(NetRegs_tx_ring_base) = configured_net.(NetRegs_tx_ring_base).
Proof. reflexivity. Qed.

(* RX advance preserves TX registers *)
Lemma rx_advance_preserves_tx_head :
  after_rx_advance.(NetRegs_tx_head) = configured_net.(NetRegs_tx_head).
Proof. reflexivity. Qed.

(* DMA descriptor: default has zero address and length *)
Lemma dma_desc_zero :
  (Build_DmaDesc (mword_of_int 0) (mword_of_int 0) (mword_of_int 0) (mword_of_int 0)).(DmaDesc_addr) = mword_of_int 0.
Proof. reflexivity. Qed.

(* Tessera — the UART console device (SSG-6): correctness proofs.
   All theorems axiom-free. *)

From Stdlib Require Import Bool ZArith.
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import SailStdpp.Operators_mwords.
Require Import uart_types.
Require Import uart_ops.

(* ---- Test vectors ---- *)

Lemma uart_default_tx_ready :
  uart_default.(UartRegs_tx_ready) = true.
Proof. reflexivity. Qed.

Lemma uart_default_rx_ready :
  uart_default.(UartRegs_rx_ready) = false.
Proof. reflexivity. Qed.

Definition test_ch : mword 8 := mword_of_int 65.  (* 'A' *)

(* Write THR: character stored, tx_ready cleared *)
Lemma uart_write_thr_stores_char :
  (uart_write_thr uart_default test_ch).(UartRegs_thr) = test_ch.
Proof. reflexivity. Qed.

Lemma uart_write_thr_clears_tx :
  (uart_write_thr uart_default test_ch).(UartRegs_tx_ready) = false.
Proof. reflexivity. Qed.

(* Tx complete: THR moves to RBR, tx_ready set, rx_ready set *)
Lemma uart_tx_complete_thr_to_rbr :
  let u1 := uart_write_thr uart_default test_ch in
  let u2 := uart_tx_complete u1 in
  u2.(UartRegs_rbr) = test_ch.
Proof. reflexivity. Qed.

Lemma uart_tx_complete_sets_tx :
  let u1 := uart_write_thr uart_default test_ch in
  let u2 := uart_tx_complete u1 in
  u2.(UartRegs_tx_ready) = true.
Proof. reflexivity. Qed.

(* Read RBR: character returned, rx_ready cleared *)
Lemma uart_read_rbr_returns_char :
  let u1 := uart_write_thr uart_default test_ch in
  let u2 := uart_tx_complete u1 in
  let (ch, u3) := uart_read_rbr u2 in
  ch = test_ch.
Proof. reflexivity. Qed.

Lemma uart_read_rbr_clears_rx :
  let u1 := uart_write_thr uart_default test_ch in
  let u2 := uart_tx_complete u1 in
  let (ch, u3) := uart_read_rbr u2 in
  u3.(UartRegs_rx_ready) = false.
Proof. reflexivity. Qed.

(* TX round-trip: write → tx_complete → read returns same character *)
Lemma uart_tx_roundtrip :
  let u1 := uart_write_thr uart_default test_ch in
  let u2 := uart_tx_complete u1 in
  let (ch, u3) := uart_read_rbr u2 in
  ch = test_ch.
Proof. reflexivity. Qed.

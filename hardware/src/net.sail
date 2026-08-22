// Tessera — the network device (SSG-7): DMA descriptor ring model.
// SPDX-License-Identifier: BSD-2-Clause
default Order dec
$include <prelude.sail>

struct DmaDesc = {
  addr : bits(48),       // DMA buffer address
  len  : bits(16),       // buffer length
  flags: bits(8),        // descriptor flags
  status: bits(8)        // completion status
}

struct NetRegs = {
  tx_ring_base : bits(48),   // TX ring base address (DMA)
  tx_ring_len  : bits(16),   // TX ring length (descriptors)
  tx_head      : bits(16),   // TX head pointer
  tx_tail      : bits(16),   // TX tail pointer
  rx_ring_base : bits(48),   // RX ring base address (DMA)
  rx_ring_len  : bits(16),   // RX ring length
  rx_head      : bits(16),   // RX head pointer
  rx_tail      : bits(16),   // RX tail pointer
  ctrl         : bits(32),   // control register
  status       : bits(32),   // status register
  irq_status   : bits(32)    // interrupt status
}

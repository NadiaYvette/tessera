// Tessera — the disk device (SSG-8): DMA command queue model.
// SPDX-License-Identifier: BSD-2-Clause
default Order dec
$include <prelude.sail>

// A disk command descriptor (similar to NVMe submission queue entry).
struct DiskCmd = {
  lba     : bits(48),      // logical block address
  len     : bits(16),      // transfer length in sectors
  opcode  : bits(8),       // read=0x20, write=0x28, flush=0x35
  flags   : bits(8),       // command flags
  status  : bits(8)        // completion status
}

// Disk registers (similar to NVMe BAR registers).
struct DiskRegs = {
  cmd_ring_base : bits(48),  // command submission ring base address (DMA)
  cmd_ring_len  : bits(16),  // command ring length
  cmd_head      : bits(16),  // command head pointer (driver writes)
  cmd_tail      : bits(16),  // command tail pointer (hardware advances)
  cmp_ring_base : bits(48),  // completion ring base address (DMA)
  cmp_ring_len  : bits(16),  // completion ring length
  cmp_head      : bits(16),  // completion head pointer (hardware writes)
  cmp_tail      : bits(16),  // completion tail pointer (driver reads)
  ctrl          : bits(32),  // control register
  status        : bits(32),  // status register
  irq_status    : bits(32)   // interrupt status
}

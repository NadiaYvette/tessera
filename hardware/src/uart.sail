// Tessera — the UART console device (SSG-6): 8250/16550-compatible register set.
// The Sail file typechecks only — uart_types.v provides the record types;
// uart.v is hand-written with Rocq definitions.
default Order dec
$include <prelude.sail>

struct UartRegs = {
  thr : bits(8),       // Transmit Holding Register (write)
  rbr : bits(8),       // Receive Buffer Register (read)
  ier : bits(4),       // Interrupt Enable Register
  iir : bits(4),       // Interrupt Identification Register (read-only)
  fcr : bits(4),       // FIFO Control Register (write-only)
  lcr : bits(8),       // Line Control Register
  mcr : bits(5),       // Modem Control Register
  lsr : bits(8),       // Line Status Register
  msr : bits(8),       // Modem Status Register
  scr : bits(8),       // Scratch Register
  dll : bits(8),       // Divisor Latch Low
  dlh : bits(8),       // Divisor Latch High
  tx_ready : bool,
  rx_ready : bool
}

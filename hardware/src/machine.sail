default Order dec

$include <prelude.sail>

// ============================================================
// Tessera hardware-state model: machine skeleton + RISC-V Sv39
// translation walk + per-core TLB + SFENCE.VMA.
// Written functionally (Sail is first-order, so memory is an
// explicit association list) so the Coq backend emits clean
// definitions for the Iris track (property2/coq).
// ============================================================

// Addresses (RISC-V Sv39: 64-bit VA, 56-bit PA, 44-bit PPN).
type vaddr = bits(64)
type paddr = bits(56)

// Mapping permissions -- the Tessera-relevant subset (read / write).
enum Perm = { None_, Read, ReadWrite }

// RISC-V Sv39 page-table entry (leaf view): V, R, W, X, U, the Svnapot N bit
// (PTE[63]), + PPN.
struct Pte = {
  valid : bool,
  read  : bool,
  write : bool,
  exec  : bool,
  user  : bool,
  napot : bool,
  ppn   : bits(44)
}

// A TLB entry: the full virtual address it was filled from, its VPN, the
// physical page number, and perms.  RISC-V matches on `vpn` only, but VIVT/VIPT
// variants index/tag by the full `vaddr` (the low-order set-index bits live in
// the page offset, which `vpn` discards) — so each entry ("cell") is coupled to
// the virtual address that produced it.
struct TlbEntry = {
  vaddr : vaddr,      // full VA the entry was filled for (VIVT/VIPT index/tag)
  vpn   : bits(27),   // Sv39 VPN = VA[38..12]
  ppn   : bits(44),
  perm  : Perm
}

// One core: the root page-table PPN (satp.PPN), its private TLB, and its
// topology placement — the hardware-thread id (hart, an SMT thread within a
// core) and the NUMA node the core belongs to (SSG-1).  The shootdown
// correctness so far is topology-agnostic; these fields are the plumbing that
// future topology-sensitive properties (SMT co-residency, NUMA locality) attach
// to.
struct Core = {
  satp_ppn : bits(44),
  tlb      : list(TlbEntry),
  hart     : int,
  node     : int
}

// Physical memory, as a sparse association list: (PTE physical address, PTE).
// The walk reads PTEs by address; a missing address means the walk faults.
struct MemEntry = {
  addr : paddr,
  pte  : Pte
}

type PageTable = list(MemEntry)

// Data RAM: byte-addressable physical memory, as a sparse association list of
// bytes (the data-side twin of PageTable).  This closes the G3 gap — the machine
// now has real data storage, so data load/store correctness is in scope.
// A missing address means an unmapped/faulting access.
struct Byte = {
  addr : paddr,
  data : bits(8)
}

type Ram = list(Byte)

// The machine: a set of cores sharing one physical memory (page-table
// descriptors plus data RAM), and a per-core IPI mailbox (SSG-3 / S2.3).
struct Machine = {
  cores : list(Core),
  mem   : PageTable,
  ram   : Ram,
  ipi   : list(bool)
}

// ---- VPN / offset extraction (Sv39) ----

val vpn2 : vaddr -> bits(9)
function vpn2(va) = va[38 .. 30]

val vpn1 : vaddr -> bits(9)
function vpn1(va) = va[29 .. 21]

val vpn0 : vaddr -> bits(9)
function vpn0(va) = va[20 .. 12]

val vpn_of : vaddr -> bits(27)
function vpn_of(va) = va[38 .. 12]

val page_offset : vaddr -> bits(12)
function page_offset(va) = va[11 .. 0]

// ---- address arithmetic ----

val pte_address : (bits(44), bits(9)) -> paddr
function pte_address(table_ppn, index) =
  sail_shiftleft(sail_zero_extend(table_ppn, 56), 12) | sail_shiftleft(sail_zero_extend(index, 56), 3)

val phys_addr : (bits(44), bits(12)) -> paddr
function phys_addr(ppn, off) =
  sail_shiftleft(sail_zero_extend(ppn, 56), 12) | sail_zero_extend(off, 56)

// ---- Svnapot (extension N bit, PTE[63]) ----
//
// A leaf PTE with the N bit set is a naturally aligned power-of-two (NAPOT)
// page.  Only the 64KiB encoding is valid: the low 4 PPN bits must be 0b1000
// (the "contiguity" pattern), and the physical page is ppn[43..4] followed by
// the 16-bit page offset VA[15..0].  This transcribes sail-riscv
// model/sys/vmem.sail (pt_walk, the Svnapot clause) and vmem_pte.sail (the
// PTE_Ext.N bitfield).

val napot_guard : bits(44) -> bool
function napot_guard(ppn) = ppn[3 .. 0] == 0b1000

val napot_phys_addr : (bits(44), vaddr) -> paddr
function napot_phys_addr(ppn, va) =
  sail_shiftleft(sail_zero_extend(ppn[43 .. 4], 56), 16) | sail_zero_extend(va[15 .. 0], 56)

// ---- PTE interpretation ----

val is_leaf : Pte -> bool
function is_leaf(pte) =
  if pte.read then true
  else if pte.write then true
  else if pte.exec then true
  else false

val perm_of_pte : Pte -> Perm
function perm_of_pte(pte) =
  if pte.write then ReadWrite
  else if pte.read then Read
  else None_

// ---- memory read ----

val read_pte : (PageTable, paddr) -> option(Pte)
function read_pte(mem, addr) = match mem {
  [||] => None(),
  e :: rest =>
    if e.addr == addr then Some(e.pte)
    else read_pte(rest, addr)
}

// ---- data RAM read / write (byte-addressable) ----

val read_byte : (Ram, paddr) -> option(bits(8))
function read_byte(ram, addr) = match ram {
  [||] => None(),
  b :: rest =>
    if b.addr == addr then Some(b.data)
    else read_byte(rest, addr)
}

val write_byte : (Ram, paddr, bits(8)) -> Ram
function write_byte(ram, addr, v) = match ram {
  [||] => struct { addr = addr, data = v } :: [||],
  b :: rest =>
    if b.addr == addr then struct { addr = addr, data = v } :: rest
    else b :: write_byte(rest, addr, v)
}

// ---- address decode (the "decode" half of the G3 gap) ----
//
// A physical address is decoded to the region that serves it before any data
// access (the data-side twin of the MMU walk's PTE interpretation).  RAM is
// served by `read_byte`/`write_byte`; MMIO is served by a device, which the
// model does not yet have (SSG-5..8), so a device access faults.  Illustrative
// one-bit split — PA[55] = 0 is RAM (the low 2^55 bytes), PA[55] = 1 is the
// device window.  The real per-platform map (QEMU virt PLIC/UART windows etc.)
// replaces this constant once devices land; what the proofs rely on is only
// that the decode step exists and is respected by loads/stores.

enum Region = { RAM, MMIO }

val decode_addr : paddr -> Region
function decode_addr(pa) =
  if pa[55] == 0b0 then RAM else MMIO

// ---- hardware page-table walk (3 levels, Sv39) ----

val translate : (Core, PageTable, vaddr) -> option((paddr, Perm))
function translate(core, mem, va) = {
  let l2 : option(Pte) = read_pte(mem, pte_address(core.satp_ppn, vpn2(va)));
  match l2 {
    None() => None(),
    Some(p2) =>
      if p2.valid then {
        if is_leaf(p2) then None()
        else {
          let l1 : option(Pte) = read_pte(mem, pte_address(p2.ppn, vpn1(va)));
          match l1 {
            None() => None(),
            Some(p1) =>
              if p1.valid then {
                if is_leaf(p1) then None()
                else {
                  let l0 : option(Pte) = read_pte(mem, pte_address(p1.ppn, vpn0(va)));
                  match l0 {
                    None() => None(),
                    Some(p0) =>
                      if p0.valid then {
                        // Reserved Sv39 encoding R=0, W=1 (an SS page when X=0, or
                        // otherwise-reserved when X=1) must fault, not translate.
                        if p0.write & not_bool(p0.read) then None()
                        else if is_leaf(p0) then {
                          // Svnapot: N=1 is a 64KiB NAPOT page (ppn[3..0] must be
                          // 0b1000, else reserved -> fault); N=0 is a normal 4KiB
                          // page.
                          if p0.napot then {
                            if napot_guard(p0.ppn) then Some((napot_phys_addr(p0.ppn, va), perm_of_pte(p0)))
                            else None()
                          } else Some((phys_addr(p0.ppn, page_offset(va)), perm_of_pte(p0)))
                        }
                        else None()
                      } else None()
                  }
                }
              } else None()
          }
        }
      } else None()
  }
}

// ---- TLB lookup / invalidation ----

val find_tlb : (list(TlbEntry), bits(27), bits(12)) -> option((paddr, Perm))
function find_tlb(entries, vpn, off) = match entries {
  [||] => None(),
  e :: rest =>
    if e.vpn == vpn then Some((phys_addr(e.ppn, off), e.perm))
    else find_tlb(rest, vpn, off)
}

val tlb_lookup : (Core, vaddr) -> option((paddr, Perm))
function tlb_lookup(core, va) = find_tlb(core.tlb, vpn_of(va), page_offset(va))

// SFENCE.VMA all: invalidate every TLB entry on this core.
val sfence_vma_all : Core -> Core
function sfence_vma_all(core) = struct {
  satp_ppn = core.satp_ppn,
  tlb      = [||],
  hart     = core.hart,
  node     = core.node
}

// SFENCE.VMA by VA: drop only entries matching the virtual page.
val filter_tlb : (list(TlbEntry), bits(27)) -> list(TlbEntry)
function filter_tlb(entries, vpn) = match entries {
  [||] => [||],
  e :: rest =>
    if e.vpn == vpn then filter_tlb(rest, vpn)
    else e :: filter_tlb(rest, vpn)
}

val sfence_vma_va : (Core, vaddr) -> Core
function sfence_vma_va(core, va) = struct {
  satp_ppn = core.satp_ppn,
  tlb      = filter_tlb(core.tlb, vpn_of(va)),
  hart     = core.hart,
  node     = core.node
}

// ---- IPI delivery (SSG-3 / S2.3) ----
//
// The shootdown so far is a functional broadcast (map sfence_vma_va over the
// cores); there is no IPI-delivery transition.  SSG-3 adds one: the leader marks
// core i's shootdown IPI delivered (deliver_ipi), and the remote only clears its
// TLB once the IPI has been delivered (receive_ipi).  The delivered bits live in
// Machine.ipi, parallel to Machine.cores.  receive_ipi's guard is the pure-model
// form of "delivery precedes ack": a remote cannot flush (ack) before delivery.

// Update list element i (recursive; out-of-range index leaves the list alone).
val list_update_bool : (list(bool), int, bool) -> list(bool)
function list_update_bool(l, i, v) = match (l, i) {
  (_ :: rest, 0) => v :: rest,
  (x :: rest, n) => x :: list_update_bool(rest, n - 1, v),
  ([||], _) => [||]
}

// Read list element i, with a default for out-of-range.
val list_nth_bool : (list(bool), int, bool) -> bool
function list_nth_bool(l, i, d) = match (l, i) {
  (x :: _, 0) => x,
  (_ :: rest, n) => list_nth_bool(rest, n - 1, d),
  ([||], _) => d
}

// deliver_ipi: the leader marks core i's shootdown IPI delivered.
val deliver_ipi : (Machine, int) -> Machine
function deliver_ipi(m, i) = struct {
  cores = m.cores,
  mem   = m.mem,
  ram   = m.ram,
  ipi   = list_update_bool(m.ipi, i, true)
}

// Walk the cores, flushing `va` from core i's TLB iff `delivered` holds (the
// delivered bit is read once by receive_ipi and carried down as a parameter).
// (The VA being flushed is the shootdown's VA; the IPI delivers the signal, the
// VA is communicated out-of-band.)
val receive_ipi_cores : (list(Core), int, bool, vaddr) -> list(Core)
function receive_ipi_cores(cores, i, delivered, va) = match (cores, i) {
  (c :: cs, 0) => (if delivered then sfence_vma_va(c, va) else c) :: cs,
  (c :: cs, n) => c :: receive_ipi_cores(cs, n - 1, delivered, va),
  ([||], _) => [||]
}

// receive_ipi: core i takes its IPI and flushes `va` from its TLB — but only if
// the IPI was delivered first (ipi[i] = true).
val receive_ipi : (Machine, int, vaddr) -> Machine
function receive_ipi(m, i, va) = struct {
  cores = receive_ipi_cores(m.cores, i, list_nth_bool(m.ipi, i, false), va),
  mem   = m.mem,
  ram   = m.ram,
  ipi   = m.ipi
}

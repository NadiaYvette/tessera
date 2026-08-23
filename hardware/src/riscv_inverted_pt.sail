// ============================================================
// Tessera — Custom RISC-V MMU extension: Inverted Page Table
// with SLB and residue-based partitioning for 56 superpage sizes.
//
// Design: g_n = K * 2^(W*n), K=256B, W=1, n in [0,55]
// Partition = n mod 4 (preserves TLB expansibility)
// Hash = additive fold of sp_vpn and partition
// SLB = POWER9-style segment cache (fundamental component)
// ============================================================

default Order dec

$include <prelude.sail>

type vaddr = bits(64)
type paddr = bits(56)
type size_log2 = bits(6)
type partition = bits(2)
type sp_vpn = bits(56)

// ============================================================
// size_log2 <-> int (Sail shift ops require int)
// ============================================================

function sz_to_int(sz : size_log2) -> int = {
  match sz {
    0b000000 => 0,  0b000001 => 1,  0b000010 => 2,  0b000011 => 3,
    0b000100 => 4,  0b000101 => 5,  0b000110 => 6,  0b000111 => 7,
    0b001000 => 8,  0b001001 => 9,  0b001010 => 10, 0b001011 => 11,
    0b001100 => 12, 0b001101 => 13, 0b001110 => 14, 0b001111 => 15,
    0b010000 => 16, 0b010001 => 17, 0b010010 => 18, 0b010011 => 19,
    0b010100 => 20, 0b010101 => 21, 0b010110 => 22, 0b010111 => 23,
    0b011000 => 24, 0b011001 => 25, 0b011010 => 26, 0b011011 => 27,
    0b011100 => 28, 0b011101 => 29, 0b011110 => 30, 0b011111 => 31,
    0b100000 => 32, 0b100001 => 33, 0b100010 => 34, 0b100011 => 35,
    0b100100 => 36, 0b100101 => 37, 0b100110 => 38, 0b100111 => 39,
    0b101000 => 40, 0b101001 => 41, 0b101010 => 42, 0b101011 => 43,
    0b101100 => 44, 0b101101 => 45, 0b101110 => 46, 0b101111 => 47,
    0b110000 => 48, 0b110001 => 49, 0b110010 => 50, 0b110011 => 51,
    0b110100 => 52, 0b110101 => 53, 0b110110 => 54, 0b110111 => 55,
    _ => 55
  }
}

// ============================================================
// Address arithmetic
// ============================================================

val sp_vpn_of : (vaddr, size_log2) -> sp_vpn
function sp_vpn_of(va, sz) = {
  let shifted : bits(64) = sail_shiftright(sail_zero_extend(va, 64), sz_to_int(sz));
  shifted[55 .. 0]
}

val page_offset_of : (vaddr, size_log2) -> bits(56)
function page_offset_of(va, sz) = {
  let all_ones : bits(56) = 0xFFFFFFFFFFFFFF;
  let mask : bits(56) = sail_shiftright(all_ones, 56 - sz_to_int(sz));
  va[55 .. 0] & mask
}

val mk_phys : (bits(52), vaddr, size_log2) -> paddr
function mk_phys(ppn, va, sz) = {
  let ppn56 : bits(56) = sail_zero_extend(ppn, 56);
  sail_shiftleft(ppn56, sz_to_int(sz)) | page_offset_of(va, sz)
}

val partition_of : size_log2 -> partition
function partition_of(sz) = sz[1 .. 0]

// Hash: additive fold
val phipt_hash : (sp_vpn, partition) -> bits(26)
function phipt_hash(sp, part) = {
  let lo : bits(26) = sp[25 .. 0];
  let mid : bits(26) = sp[51 .. 26];
  let hi : bits(26) = (0b00000000000000000000 @ part) @ sp[55 .. 52];
  (lo + mid) + hi
}

// ============================================================
// SLB (Segment Lookaside Buffer) — POWER9-style
// ============================================================

struct SlbEntry = {
  valid  : bool,
  vsid   : bits(36),
  ppn    : bits(20),
  size   : bits(4),
  perms  : bits(4),
  global : bool,
  asid   : bits(16)
}

type Slb = list(SlbEntry)

val slb_lookup : (Slb, vaddr, bits(16)) -> option(SlbEntry)
function slb_lookup(slb, va, asid) = match slb {
  [||] => None(),
  e :: rest =>
    if e.valid & (e.vsid == va[63 .. 28]) & (e.global | e.asid == asid) then
      Some(e)
    else
      slb_lookup(rest, va, asid)
}

// ============================================================
// Inverted Page Table (PHIPT)
// ============================================================

struct PhiPtEntry = {
  valid  : bool,
  sp_vpn : sp_vpn,
  ppn    : bits(52),
  size   : size_log2,
  perms  : bits(4),
  global : bool,
  asid   : bits(16)
}

struct PhiPt = {
  entries  : list(PhiPtEntry),
  log_size : bits(26)
}

val phipt_probe : (list(PhiPtEntry), sp_vpn, size_log2, bits(16), int) -> option(PhiPtEntry)
function phipt_probe(entries, sp, sz, asid, depth) = match entries {
  [||] => None(),
  e :: rest =>
    if depth >= 64 then None()
    else if e.valid & (e.sp_vpn == sp) & (e.size == sz) & (e.global | e.asid == asid) then
      Some(e)
    else
      phipt_probe(rest, sp, sz, asid, depth + 1)
}

val phipt_lookup : (PhiPt, vaddr, size_log2, bits(16)) -> option(PhiPtEntry)
function phipt_lookup(pt, va, sz, asid) = {
  let sp : sp_vpn = sp_vpn_of(va, sz);
  phipt_probe(pt.entries, sp, sz, asid, 0)
}

val phipt_insert : (PhiPt, PhiPtEntry) -> PhiPt
function phipt_insert(pt, entry) = struct {
  entries  = entry :: pt.entries,
  log_size = pt.log_size
}

val phipt_filter : (list(PhiPtEntry), vaddr, bits(16)) -> list(PhiPtEntry)
function phipt_filter(entries, va, asid) = match entries {
  [||] => [||],
  e :: rest =>
    if e.valid & (sp_vpn_of(va, e.size) == e.sp_vpn) & (e.global | e.asid == asid) then
      phipt_filter(rest, va, asid)
    else
      e :: phipt_filter(rest, va, asid)
}

val phipt_invalidate : (PhiPt, vaddr, bits(16)) -> PhiPt
function phipt_invalidate(pt, va, asid) = struct {
  entries  = phipt_filter(pt.entries, va, asid),
  log_size = pt.log_size
}

// All 56 size values as a list (largest first for Zipf optimization)
// Sail lists use :: (cons) and [||] (nil)
val all_sizes : unit -> list(size_log2)
function all_sizes(_) =
  0b110111 :: 0b110110 :: 0b110101 :: 0b110100 :: 0b110011 :: 0b110010 :: 0b110001 :: 0b110000 ::
  0b101111 :: 0b101110 :: 0b101101 :: 0b101100 :: 0b101011 :: 0b101010 :: 0b101001 :: 0b101000 ::
  0b100111 :: 0b100110 :: 0b100101 :: 0b100100 :: 0b100011 :: 0b100010 :: 0b100001 :: 0b100000 ::
  0b011111 :: 0b011110 :: 0b011101 :: 0b011100 :: 0b011011 :: 0b011010 :: 0b011001 :: 0b011000 ::
  0b010111 :: 0b010110 :: 0b010101 :: 0b010100 :: 0b010011 :: 0b010010 :: 0b010001 :: 0b010000 ::
  0b001111 :: 0b001110 :: 0b001101 :: 0b001100 :: 0b001011 :: 0b001010 :: 0b001001 :: 0b001000 ::
  0b000111 :: 0b000110 :: 0b000101 :: 0b000100 :: 0b000011 :: 0b000010 :: 0b000001 :: 0b000000 :: [||]

// Search list of sizes for a match
val phipt_search_list : (PhiPt, vaddr, bits(16), list(size_log2)) -> option(PhiPtEntry)
function phipt_search_list(pt, va, asid, sizes) = match sizes {
  [||] => None(),
  sz :: rest =>
    match phipt_lookup(pt, va, sz, asid) {
      Some(e) => Some(e),
      None()  => phipt_search_list(pt, va, asid, rest)
    }
}

// ============================================================
// TLB with residue-based partitioning
// ============================================================

struct PhiTlbEntry = {
  valid     : bool,
  sp_vpn    : sp_vpn,
  ppn       : bits(52),
  size      : size_log2,
  perms     : bits(4),
  asid      : bits(16),
  partition : partition
}

type PhiTlb = list(PhiTlbEntry)

val phi_covers : (PhiTlbEntry, vaddr) -> bool
function phi_covers(e, va) = sp_vpn_of(va, e.size) == e.sp_vpn

val phi_tlb_find_best : (PhiTlb, vaddr, bits(16), option(PhiTlbEntry)) -> option(PhiTlbEntry)
function phi_tlb_find_best(tlb, va, asid, best) = match tlb {
  [||] => best,
  e :: rest =>
    if e.valid & phi_covers(e, va) & (e.asid == asid) then {
      let best' : option(PhiTlbEntry) = match best {
        None() => Some(e),
        Some(b) => if sz_to_int(e.size) > sz_to_int(b.size) then Some(e) else Some(b)
      };
      phi_tlb_find_best(rest, va, asid, best')
    } else
      phi_tlb_find_best(rest, va, asid, best)
}

val phi_tlb_lookup : (PhiTlb, vaddr, bits(16)) -> option(PhiTlbEntry)
function phi_tlb_lookup(tlb, va, asid) = {
  phi_tlb_find_best(tlb, va, asid, None())
}

val phi_tlb_flush : (PhiTlb, vaddr, bits(16)) -> PhiTlb
function phi_tlb_flush(tlb, va, asid) = match tlb {
  [||] => [||],
  e :: rest =>
    if e.valid & phi_covers(e, va) & (e.asid == asid) then
      phi_tlb_flush(rest, va, asid)
    else
      e :: phi_tlb_flush(rest, va, asid)
}

// ============================================================
// Translation: TLB -> SLB -> PHIPT
// ============================================================

val riscv_inverted_translate : (Slb, PhiPt, PhiTlb, vaddr, bits(16)) -> option((paddr, bits(4)))
function riscv_inverted_translate(slb, pt, tlb, va, asid) = {
  match phi_tlb_lookup(tlb, va, asid) {
    Some(e) => Some((mk_phys(e.ppn, va, e.size), e.perms)),
    None() =>
      match slb_lookup(slb, va, asid) {
        Some(_seg) =>
          match phipt_search_list(pt, va, asid, all_sizes(())) {
            Some(e) => Some((mk_phys(e.ppn, va, e.size), e.perms)),
            None()  => None()
          },
        None() =>
          match phipt_search_list(pt, va, asid, all_sizes(())) {
            Some(e) => Some((mk_phys(e.ppn, va, e.size), e.perms)),
            None()  => None()
          }
      }
  }
}

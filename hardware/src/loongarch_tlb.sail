default Order dec

$include <prelude.sail>

// ============================================================
// Tessera — third MMU variant: the LoongArch software-refill TLB.
//
// LoongArch (like MIPS) has **no hardware page-table walker**: a TLB miss
// traps to the OS, whose refill handler loads an entry (`tlbwr`/`tlbwi`).
// The trust line flips the same way as variant 2 (`mips_tlb.sail`) — "the
// MMU walks the table thus" becomes a *theorem about our software refill
// handler* (`la_refill_lookup_covers`, proved in loongarch_tlb_proofs.v).
//
// The two features that differ from MIPS (and from RISC-V Sv39, variant 1):
//
//   1. **Page size is a per-entry `ps` field** (the page shift), not a
//      PageMask decode.  On MIPS the OS writes a PageMask run-of-1s and the
//      hardware derives `2^(base_shift + even-count)`; on LoongArch the
//      refill handler stores `PS` directly (QEMU `fill_tlb_entry`), so the
//      page size is `2^ps`.  The valid `ps` values are constrained by
//      `CSR_PRCFG2` (QEMU `check_ps`), an OS/CSR concern outside the TLB
//      match/translate logic modelled here.
//   2. **Odd/even pair** — one TLB entry covers *two adjacent* pages of size
//      `2^ps` (QEMU's "the vpn is the virtual page number divided by 2").  The
//      VPPN field is VA[47:13] (35 bits); the match compares
//      `va[47:ps+1] == vppn[34:ps-12]`, and bit `ps` of the VA selects the
//      even (pfn0) or odd (pfn1) half.
//
// Physical addresses are 48-bit (PALEN); the PPN field is PTE[47:12] (36
// bits, QEMU `FIELD(TLBENTRY_64, PPN, 12, 36)`), so the low `ps-12` PPN bits
// are software bits masked off before `pa = pfn[35:ps-12] @ va[ps-1:0]`.
//
// Provenance: ~/src/QEMU target/loongarch/{tcg/tlb_helper,cpu_helper}.c —
// `fill_tlb_entry`/`loongarch_tlb_search_cb`/`loongarch_check_pte` (the
// `nadia.chambers/page-grain-001` branch).
// ============================================================

type vaddr = bits(64)
type paddr = bits(48)

// ---- the TLB entry and the software-refill lookup ----

struct LaEntry = {
  vppn : bits(35),   // VA[47:13] — the pair's virtual page number / 2
  ps   : int,        // page shift: page size = 2^ps
  pfn0 : bits(36),   // even-page PPN (PTE[47:12])
  pfn1 : bits(36)    // odd-page  PPN (PTE[47:12])
}

// The VPPN half of the match: VA[47:13].
val la_vppn_of : vaddr -> bits(35)
function la_vppn_of(va) = va[47 .. 13]

// Page-size-aware match (odd/even pair): va[47:ps+1] == vppn[34:ps-12].
// Expressed with fixed-width shifts: place vppn at VA bits [13:47]
// (zero_extend then shiftl 13) and shift both sides right by ps+1, so the
// widths are static (variable subranges are not first-class in Sail).
val la_covers : (LaEntry, vaddr) -> bool
function la_covers(e, va) =
  sail_shiftright(va[47 .. 0], e.ps + 1) ==
    sail_shiftright(sail_shiftleft(sail_zero_extend(e.vppn, 48), 13), e.ps + 1)

// Translation: pfn[35:ps-12] @ va[ps-1:0], with bit ps of the VA selecting
// the even (pfn0) / odd (pfn1) half of the pair.
val la_pa : (LaEntry, vaddr) -> paddr
function la_pa(e, va) = {
  let ps = e.ps;
  let odd : bool = sail_shiftright(va, ps)[0 .. 0] == 0b1;
  let pfn : bits(36) = if odd then e.pfn1 else e.pfn0;
  let pfn_hi = sail_shiftright(pfn, ps - 12);
  let off = sail_shiftright(sail_shiftleft(va, 64 - ps), 64 - ps);
  sail_shiftleft(sail_zero_extend(pfn_hi, 48), ps) |
    sail_zero_extend(off[47 .. 0], 48)
}

// The software refill handler's effect: install/replace the entry.
val la_refill : (LaEntry, list(LaEntry)) -> list(LaEntry)
function la_refill(e, tlb) = e :: tlb

// The software invalidation: drop every entry that covers `va`
// (QEMU `invalidate_tlb`/`helper_invtlb_*`, the LoongArch `sfence` analog).
val la_flush : (vaddr, list(LaEntry)) -> list(LaEntry)
function la_flush(va, tlb) = match tlb {
  [||] => [||],
  e :: rest => if la_covers(e, va) then la_flush(va, rest) else e :: la_flush(va, rest)
}

// TLB lookup: first entry that covers the VA translates it.
val la_lookup : (list(LaEntry), vaddr) -> option(paddr)
function la_lookup(tlb, va) = match tlb {
  [||] => None(),
  e :: rest => if la_covers(e, va) then Some(la_pa(e, va)) else la_lookup(rest, va)
}

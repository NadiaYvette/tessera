default Order dec

$include <prelude.sail>

// ============================================================
// Tessera — fourth MMU variant: the AArch64 TLB
// (block descriptors + contpte + FEAT_D128).
//
// Variants 1 (`machine.sail`, RISC-V Sv39) and this one are
// *hardware-walker* architectures: on a TLB miss the MMU walks the page
// table and refills the TLB.  AArch64's page-size menu is richer than
// Sv39's fixed 4 KB/2 MB/1 GB, and its superpage machinery is exactly
// the territory the pgcl catalog lives in:
//
//   1. **Block descriptors** — a level < FINAL_LEVEL descriptor is a
//      *block* (a superpage) whose size is
//      `granulebits + (FINAL_LEVEL - level) * (granulebits - descsizelog2)`.
//      4 KB granule: L3 page = 4 KB, L2 block = 2 MB, L1 block = 1 GB,
//      L0 block = 512 GB.  (MIPS got its spectrum from PageMask's
//      even-run decode; LoongArch from a per-entry `ps`; AArch64 from the
//      *walk level* × the *granule/descriptor-size* pair.)
//   2. **contpte (CONT bit)** — a contiguous hint extends the effective
//      page by `ContiguousSize` extra address bits.
//   3. **StageOA** — output address = descriptor `baseaddress[55..ia_msb]`
//      @ input address `ia[ia_msb-1..0]`, with `ia_msb = translation_size
//      + (contig ? contiguous_size : 0)`.
//
// The transcription is (near-verbatim) from the vendored `sail-arm` model:
// `third_party/sail-arm/arm-v9.4-a/src/v8_base.sail` — `ContiguousSize`
// (l. 19962), `TGxGranuleBits` (l. 20008), `TranslationSize` (l. 20026),
// `StageOA` (l. 20038).  See doc/aarch64-translation.md.
//
// The two deviations from `v8_base.sail`, both for totality (no `undefined`,
// no `assert`, hence no axioms in the generated Rocq):
//   - `contiguous_size` returns 0 for levels on which CONT is architecturally
//     reserved (the original asserts); the walker never sets `contig` there.
//   - `TGx` is a 3-constructor enum with no wildcard case.
// ============================================================

type vaddr = bits(64)
type paddr = bits(56)

// ---- the translation granule (TGx) and the size machinery ----

enum TGx = {TGx_4KB, TGx_16KB, TGx_64KB}

val tgx_granule_bits : TGx -> int
function tgx_granule_bits(tgx) = match tgx {
  TGx_4KB  => 12,
  TGx_16KB => 14,
  TGx_64KB => 16
}

// FEAT_D128: 16-byte (128-bit) descriptors (descsizelog2 = 4) — the
// VMSAv9-128 translation system — vs the base 8-byte descriptors
// (descsizelog2 = 3).  `d128` is the descriptor-width flag.  Note this is
// *not* TCR_ELx.DS == 1: DS is FEAT_LPA2, which keeps 8-byte descriptors.
val desc_size_log2 : bool -> int
function desc_size_log2(d128) = if d128 then 4 else 3

// FINAL_LEVEL = 3 (the last walk level).  A descriptor at level < 3 is a
// block (superpage); `TranslationSize` returns its effective page size.
val translation_size : (bool, TGx, int) -> int
function translation_size(d128, tgx, level) = {
  let granulebits  = tgx_granule_bits(tgx);
  let descsizelog2 = desc_size_log2(d128);
  granulebits + (3 - level) * (granulebits - descsizelog2)
}

// CONT bit -> extra low address bits (log2 of the # of contiguous entries).
// Returns 0 on the architecturally-reserved levels (the original asserts).
val contiguous_size : (bool, TGx, int) -> int
function contiguous_size(d128, tgx, level) = {
  if d128 then {
    match tgx {
      TGx_4KB  => if level == 1 then 2 else if (level == 2 | level == 3) then 4 else 0,
      TGx_16KB => if level == 1 then 2 else if level == 2 then 4 else if level == 3 then 6 else 0,
      TGx_64KB => if level == 2 then 6 else if level == 3 then 4 else 0
    }
  } else {
    match tgx {
      TGx_4KB  => if (level == 1 | level == 2 | level == 3) then 4 else 0,
      TGx_16KB => if level == 2 then 5 else if level == 3 then 7 else 0,
      TGx_64KB => if (level == 2 | level == 3) then 5 else 0
    }
  }
}

// ---- the TLB entry and the hardware-walker refill ----

struct AaEntry = {
  vatag  : bits(44),  // VA[55:12] — the address tag
  oabase : bits(44),  // OA[55:12] — the output-address base
  tgx    : TGx,       // translation granule (4 KB / 16 KB / 64 KB)
  level  : int,       // walk level (0,1,2,3); < 3 is a block/superpage
  d128   : bool,      // FEAT_D128 16-byte descriptor (VMSAv9-128)
  contig : bool       // CONT bit set (contiguous hint)
}

// ia_msb = translation_size + (contig ? contiguous_size : 0): the boundary
// between the translated high bits and the passed-through low input bits.
val aa_ia_msb : AaEntry -> int
function aa_ia_msb(e) = {
  let tsize = translation_size(e.d128, e.tgx, e.level);
  let csize = if e.contig then contiguous_size(e.d128, e.tgx, e.level) else 0;
  tsize + csize
}

// Coverage: va[55:ia_msb] == vatag[55:ia_msb] (vatag lives at VA[55:12]).
// Expressed with fixed-width shifts (variable subranges are not first-class
// in Sail), as in `la_covers`: place vatag at VA bits [12:55] and shift both
// sides right by ia_msb.
val aa_covers : (AaEntry, vaddr) -> bool
function aa_covers(e, va) = {
  let ia_msb = aa_ia_msb(e);
  sail_shiftright(va, ia_msb) ==
    sail_shiftright(sail_shiftleft(sail_zero_extend(e.vatag, 64), 12), ia_msb)
}

// StageOA: oabase[55:ia_msb] @ va[ia_msb-1:0].  The high `56-ia_msb` output
// bits come from the descriptor base address (oabase at OA[55:12], masked to
// OA[55:ia_msb]); the low `ia_msb` bits are the input address's page offset.
val aa_pa : (AaEntry, vaddr) -> paddr
function aa_pa(e, va) = {
  let ia_msb = aa_ia_msb(e);
  let oa_hi = sail_shiftright(sail_shiftleft(sail_zero_extend(e.oabase, 56), 12), ia_msb);
  let off   = sail_shiftright(sail_shiftleft(va, 64 - ia_msb), 64 - ia_msb);
  sail_shiftleft(oa_hi, ia_msb) | sail_zero_extend(off[55 .. 0], 56)
}

// The hardware walker's refill: install/replace the entry.
val aa_refill : (AaEntry, list(AaEntry)) -> list(AaEntry)
function aa_refill(e, tlb) = e :: tlb

// TLBI (invalidate by VA): drop every entry that covers `va`
// (`TLBI VALE1/VALE2/...`, QEMU `helper_tlbi_*` / `invalidate_tlb`).
val aa_flush : (vaddr, list(AaEntry)) -> list(AaEntry)
function aa_flush(va, tlb) = match tlb {
  [||] => [||],
  e :: rest => if aa_covers(e, va) then aa_flush(va, rest) else e :: aa_flush(va, rest)
}

// TLB lookup: first entry that covers the VA translates it.
val aa_lookup : (list(AaEntry), vaddr) -> option(paddr)
function aa_lookup(tlb, va) = match tlb {
  [||] => None(),
  e :: rest => if aa_covers(e, va) then Some(aa_pa(e, va)) else aa_lookup(rest, va)
}

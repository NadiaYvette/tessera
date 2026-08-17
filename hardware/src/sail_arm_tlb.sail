default Order dec

$include <prelude.sail>

// ============================================================
// Tessera — differential oracle: the vendored sail-arm page-size
// machinery, extracted *verbatim* (modulo totality) from
// `third_party/sail-arm/arm-v9.4-a/src/v8_base.sail`.
//
// The AArch64 variant (`aarch64_tlb.sail`) was transcribed from this same
// source, but flattened: `bool` for the `bits(1)` d128/contiguous flags,
// an `int` walk level, and fixed-width shifts in place of variable
// subranges.  This file keeps sail-arm's *original* shape — `bits(1)`
// flags and the variable-subrange `baseaddr[55 .. ia_msb] @ ia[ia_msb-1 .. 0]`
// — so `aarch64_sail_oracle.v` can prove the two transcriptions agree
// (general theorems for the Z-valued size functions; `vm_compute` vectors
// for the bit-vector `StageOA`).
//
// The only deviations from `v8_base.sail` are for totality (no `undefined`,
// no `assert`, hence no axioms in the generated Rocq), and one cosmetic
// rename (`TGx` -> `SaTGx`) so the two models can be imported together in
// the same Rocq file without an inductive-name collision:
//   - `ContiguousSize`'s `assert(level == ...)` and dead `_ => undefined`
//     become `0` for architecturally-reserved levels (the walker never sets
//     `contiguous` there).
//   - `TranslationSize`/`StageOA` are transcribed 1:1 (the `FINAL_LEVEL`
//     constant `3` is inlined, as in aarch64_tlb.sail).
//
// Source lines: `ContiguousSize` (l. 19962), `TGxGranuleBits` (l. 20008),
// `TranslationSize` (l. 20026), `StageOA` (l. 20038).
// ============================================================

type vaddr = bits(64)
type paddr = bits(56)

// v8_base.sail l. 2497: `enum TGx = {TGx_4KB, TGx_16KB, TGx_64KB}` (renamed).
enum SaTGx = {SaTGx_4KB, SaTGx_16KB, SaTGx_64KB}

// v8_base.sail l. 20008: `TGxGranuleBits`.
val sa_tgx_granule_bits : SaTGx -> int
function sa_tgx_granule_bits(tgx) = match tgx {
  SaTGx_4KB  => 12,
  SaTGx_16KB => 14,
  SaTGx_64KB => 16
}

// v8_base.sail l. 19962: `ContiguousSize` (d128 : bits(1), tgx, level).
// Totalized: reserved-level `assert`/`undefined` -> 0.
val sa_contiguous_size : (bits(1), SaTGx, int) -> int
function sa_contiguous_size(d128, tgx, level) = {
  if d128 == 0b1 then {
    match tgx {
      SaTGx_4KB  => if level == 1 then 2 else if (level == 2 | level == 3) then 4 else 0,
      SaTGx_16KB => if level == 1 then 2 else if level == 2 then 4 else if level == 3 then 6 else 0,
      SaTGx_64KB => if level == 2 then 6 else if level == 3 then 4 else 0
    }
  } else {
    match tgx {
      SaTGx_4KB  => if (level == 1 | level == 2 | level == 3) then 4 else 0,
      SaTGx_16KB => if level == 2 then 5 else if level == 3 then 7 else 0,
      SaTGx_64KB => if (level == 2 | level == 3) then 5 else 0
    }
  }
}

// v8_base.sail l. 20026: `TranslationSize` (FINAL_LEVEL = 3 inlined).
val sa_translation_size : (bits(1), SaTGx, int) -> int
function sa_translation_size(d128, tgx, level) = {
  let granulebits  = sa_tgx_granule_bits(tgx);
  let descsizelog2 = if d128 == 0b1 then 4 else 3;
  granulebits + (3 - level) * (granulebits - descsizelog2)
}

// `StageOA` (v8_base.sail l. 20038) is *not* extracted here: its address
// computation `baseaddress.address[55 .. ia_msb] @ ia[ia_msb - 1 .. 0]` is a
// variable subrange, which sail-arm can only typecheck behind
// `assert(constraint(0 <= ia_msb <= 55))` — an axiom in the generated Rocq.
// `aarch64_tlb.sail` therefore re-expresses it with fixed-width shifts
// (`aa_pa`); the StageOA diff is done in aarch64_sail_oracle.v via a direct
// transcription using SailStdpp's `subrange_vec_dec`/`concat_vec_dec` and
// pinned by `vm_compute` vectors (the general bit-vector identity is blocked
// on the abstract MachineWord interface — see loongarch-software-refill.md).

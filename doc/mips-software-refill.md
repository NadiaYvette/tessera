# Second MMU variant: MIPS software-refill TLB (+ PageGrain 1 KiB)

## Why this is the second variant

`hardware/src/machine.sail` models a **hardware page-table walker** (RISC-V
Sv39): the MMU reads PTEs itself.  MIPS has **no hardware walker** — on a TLB
miss the CPU traps to the OS, whose refill handler consults whatever structure it
likes and loads an entry (`tlbwr`/`tlbwi`).  That flips the trust line
(`mmu-variants.md` §1, `formalization-status.md`):

| | RISC-V Sv39 (variant 1) | MIPS (variant 2) |
|---|---|---|
| who fills the TLB | hardware walker | **our refill handler** |
| "the MMU walks the table thus" | trusted (§5) | **a theorem about our code** |
| page-size menu | {4K, 64K (Svnapot)} | **{4^k · M}, dense ×4 spectrum** |
| base page M | 4 KiB | **1 KiB** (Config3.SP ∧ PageGrain.ESP) |

So the second variant is *both* of the two orthogonal axes of `mmu-variants.md`:
axis 1 = software refill, axis 2 = a **dense page-size spectrum** down to 1 KiB.

## PageMask semantics (MD00091 §9.14, from ~/src/QEMU target/mips)

`compute_pagemask` (`tcg/system/cp0_helper.c:872`):

- The **Mask field** is PageMask[28:13] (16 bits).  Under ESP (1 KiB enabled)
  it is extended **downwards** by **MaskX** = PageMask[12:11] (2 bits) → 18 bits.
- A **valid** encoding is a *run of 1s from the low end* (i.e. `mask =
  0b000...011...1`) with an **even** count of 1s.  `cto32(mask)` = the count,
  `(mask >> count) == 0`, and `(count & 1) == 0` must all hold; else the write
  falls back to the architectural default (mask 0).
- Page size = `2^(base_shift + count)` where `base_shift = 12` (4 KiB) normally
  and `base_shift = 10` (1 KiB) under ESP.  The count is even, so the spectrum
  is `{1 K, 4 K, 16 K, 64 K, 256 K, 1 M, 4 M, 16 M, 64 M, 256 M, …}` — exactly
  the dense ×4 menu the clustering work wants.

`r4k_fill_tlb` (`tcg/system/tlb_helper.c:52`):

- `pfn_shift = esp ? 10 : 12`.
- The VPN keeps EntryHi[12:11] (`VPN2X`) under ESP — those carry VA[12:11] for
  1 KiB pages; under ESP=0 they are RAZ/WI.
- `PFN = (EntryLo.PFN & ~mask) << pfn_shift` where `mask = PageMask >> lsb`
  (`lsb = 13` normally, `11` under ESP).
- The **match** (`tlb_helper.c:214`): `mask = PageMask | 0x7FF` (bits [10:0]
  always the 1 K-pair offset), then `VPN & ~mask == va & ~mask`.  Bits [10:0]
  are *always* page offset — this is what makes 1 KiB the floor under ESP.

## Model shape (as built)

A second Sail file `hardware/src/mips_tlb.sail`, self-contained, parallel to
`machine.sail`, generated into `hardware/rocq/mips_tlb.v`/`mips_tlb_types.v`.
It elides the even/odd `EntryLo0/1` two-page pairing (not the
Tessera-relevant essence) and models the parts that *differ* from variant 1:

1. **`compute_mask_level (reg : mword 29) (esp : bool) : option Z`** — the
   faithful run-of-1s/even-count predicate over the 18-bit `Mask @ MaskX` field
   (extracted by `mips_mask_field`); `None` for an invalid encoding, `Some k`
   (k = count of 1s) otherwise.  `cto18 = count_trailing_zeros (not_vec v)`
   transcribes QEMU's `cto32`.
2. **`MipsEntry = { vpn : mword 28, pfn : mword 44, level : Z, esp : bool }`** —
   one TLB entry, page size `2^(base_shift + level)`.
3. **`mips_lookup : (list(MipsEntry), vaddr) -> option(paddr)`** — page-size-aware
   match (`mips_covers`: `vpn[27..level] == va[39..(12+level)]`, high VPN bits)
   and translation `mips_pa` (`pfn @ va[11+level .. 0]`) — the MIPS analog of
   variant 1's `tag_eq`/`tlb_pa` over a *spectrum*, not a single NAPOT bit.
4. **`mips_refill : (MipsEntry, list(MipsEntry)) -> list(MipsEntry)`** — the
   software handler's effect (add/replace the entry), the object of the
   refill-handler-correctness theorem.
5. **`mips_vpn2x (va : mword 64) : mword 2`** — `EntryHi[12:11]`
   (`subrange_vec_dec va 12 11`), the 1 KiB VPN2X field; `mips_base_shift`/
   `mips_page_shift` carry the ESP-dependent base (`true → 10`, `false → 12`).

## Theorems proved (the point of the variant)

All in `hardware/rocq/mips_tlb_proofs.v`, axiom-free against the generated model:

1. **Page-size spectrum** — `compute_mask_level` accepts exactly the `{4^k · M}`
   encodings (even run) and rejects odd counts / non-runs
   (`compute_mask_level_unfold`, `compute_mask_level_some_even`).  Executable
   vectors pin 1 KiB, 4 KiB, 16 KiB acceptance and odd/non-run rejection
   (incl. the ESP 1 KiB base via `mips_page_shift true 0 = 10`).
2. **Page-size-aware match** — a `level = 0` (1 KiB, esp) entry matches a VA
   differing only in bits [11:0] and translates to `pfn @ VA[11:0]`; a 4 KiB
   entry does *not* match a VA 1 KiB apart.  (MIPS twin of `find_tlb_napot_leaf`.)
3. **Refill-handler correctness** — `mips_lookup (mips_refill e tlb) va =
   Some (mips_pa e va)` when `e` covers `va`: the trust-boundary win, stated as a
   fact about the *software* refill rather than a trusted hardware walker.
4. **VPN2X (1 KiB) instantiation** — `test_vector_vpn2x_0..3` pin all four
   `EntryHi[12:11]` decodings; `test_vector_base_shift_*`/
   `test_vector_page_shift_*` pin the ESP-dependent page-shift spectrum.

## QEMU differential oracle (`mips_qemu_oracle.v`)

The decode is **diff-tested** against QEMU's `compute_pagemask`
(`~/src/QEMU` branch `nadia.chambers/page-grain-001`, `cp0_helper.c:872`):

- `qemu_*` definitions transcribe QEMU's C line-by-line (`qemu_accept`,
  `qemu_compute_pagemask`, `qemu_pfn`/`qemu_offset_mask`/`qemu_pa`,
  `qemu_match_mask`/`qemu_match`); `qemu_extract` shares the model's
  `mips_mask_field` (the shared field-extraction primitive, per the
  `conformance.v` precedent).
- `qemu_cto_cto18` bridges QEMU's `cto32` to the model's `cto18`.
- **`compute_mask_level_conforms`** — for all `reg`, `esp`, the Sail decode
  equals the QEMU transcription's accept-or-default result.
- 16 executable diff vectors: decode agreement (lvl0/2/4, odd, non-run,
  esp-lvl2), PA translation (1k/4k/16k/esp-4k) and page-size-aware match
  (1 KiB pairing, 4 KiB next-page, 16 KiB superpage).

## Shootdown integration (`mips_tlb_proofs.v`)

The MIPS variant now composes with the coherence/shootdown story.  On MIPS there
is no hardware walker to "drop a PTE"; unmap is a *software* decision followed by
a software TLB invalidation — `mips_flush` (the tlbp/tlbwi/tlbwr analog of
`sfence_vma_va`), generated from `mips_tlb.sail`.  The MIPS twins of the
variant-1 theorems are proved axiom-free:

- **`mips_flush_clears`** — after dropping every entry that covers `va`, no
  lookup answers for `va` (the MIPS `sfence_vma_va_clears`).
- **`mips_unmap_without_flush_breaks_coherence`** — *without* the flush, a
  covering stale entry still answers `Some (mips_pa e va)` (the MIPS
  `unmap_without_flush_breaks_coherence`).
- **`mips_refill_flush_composes`** — refill an entry covering `va`, then flush
  `va`: the refill is undone and the lookup is clean.  This is the composition
  of the refill-handler theorem (§"refill-handler correctness") with the flush.
- **`mips_shootdown_correct`** — broadcasting the flush to every core's TLB
  (`mips_shootdown = map (mips_flush va)`) leaves no core answering for `va`
  (the MIPS `shootdown_correct`).

Plus two `vm_compute` vectors (`test_vector_mips_flush`,
`test_vector_mips_flush_preserves_other`).

The existing coherence/shootdown machinery (variant 1) is left untouched; this is
an additive second module demonstrating the parameterization point (H4), now
fully Sail-transcribed, oracle-diff-tested, 1 KiB (VPN2X/ESP)-instantiated, and
integrated with the coherence/shootdown theorems.

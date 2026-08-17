# Fourth MMU variant: AArch64 VMSAv8-64 (block descriptors + contpte + TLBI)

## Why this is the fourth variant

Unlike MIPS/LoongArch (software refill), AArch64 is a **hardware-walker**
architecture like the RISC-V `machine.sail` variant — but its page-size menu is
richer and its superpage machinery is exactly the territory the pgcl catalog
lives in.  The vendored `sail-arm` model (a full ISA model, not a focused MMU
extract) is the oracle; this note maps its translation semantics and sketches
the focused model that drops in behind the same interface as
`mips_tlb.sail`/`loongarch_tlb.sail`.

## Where the semantics live (vendored `sail-arm`)

`third_party/sail-arm/arm-v9.4-a/src/v8_base.sail` (57k lines) contains the
VMSA translation in the `v8_base` fragment.  The key fragments:

| symbol | line | role |
|---|---|---|
| `struct TLBRecord` | 2637 | the TLB entry record (VA tag + OA + attrs) |
| `TranslationRegime` | 12344 | EL0/1/2/3 stage-1 regime selection |
| `DecodeGPTContiguous` | 19587 | GPT (stage-2-like) contiguous decode |
| `ContiguousSize` | 19962 | CONT bit → extra address bits (`log2 #entries`) |
| `TGxGranuleBits` | 20008 | 4 KB→12, 16 KB→14, 64 KB→16 |
| `TranslationSize` | 20026 | block/page size = `granulebits + (FINAL_LEVEL−level)·(granulebits−descsizelog2)` |
| `StageOA` | 20038 | output address = `baseaddress[55..ia_msb] @ ia[ia_msb−1..0]` |

## The two AArch64 superpage mechanisms (the point of the variant)

1. **Block descriptors** — a level `< FINAL_LEVEL` descriptor is a *block* (a
   superpage).  `TranslationSize` gives the block size:

   ```
   granulebits   = TGxGranuleBits tgx                // 12 | 14 | 16
   descsizelog2  = d128 ? 4 : 3                      // DS2 (LPA2, 16 B) vs 8 B
   translation_size = granulebits + (FINAL_LEVEL − level) * (granulebits − descsizelog2)
   ```

   4 KB granule, FINAL_LEVEL=3: L3 page = 4 KB, L2 block = 2 MB, L1 block =
   1 GB, L0 block = 512 GB.  (MIPS got its spectrum from PageMask's even-run
   decode; LoongArch from a per-entry `ps`; AArch64 from the *walk level* × the
   *granule/descriptor-size* pair.)

2. **contpte (CONT bit)** — a level-3 (or level-2) contiguous hint extends the
   effective page by `ContiguousSize` extra address bits (the `d128` variant is
   the `FEAT_LPA2` DS2 encoding):

   ```
   contiguous_size d128 tgx level =              // 4 KB: 16 entries (csize 4)
     if d128 then 4KB→(level1:2 | level2:4 | level3:4); 16KB→(2|4|6); 64KB→(6|4)
     else         4KB→(level1:4 | level2:4 | level3:4); 16KB→(level2:5|level3:7); 64KB→5
   ```

3. **StageOA** — the output address is the descriptor's `baseaddress` high bits
   plus the low `ia_msb` input-address bits, where `ia_msb = translation_size +
   (contig ? contiguous_size : 0)`:

   ```
   stage_oa(ia, baseaddress) = baseaddress[55..ia_msb] @ ia[ia_msb−1..0]
   ```

This is the AArch64 twin of the MIPS/LoongArch `mips_pa`/`la_pa`, and the direct
home of the pgcl #9 (contpte fold loses sub-offset) and #10 (TLBI stride)
failure modes.

## Model shape (`hardware/src/aarch64_tlb.sail`, implemented)

- `TGx` enum; `tgx_granule_bits`, `contiguous_size`, `translation_size` —
  transcribed (nearly verbatim) from `v8_base.sail`.
- `AaEntry = { vatag : mword 44, oabase : mword 44, tgx, level : Z, d128 : bool,
  contig : bool }` — one TLB entry (VA[55:12] tag + OA[55:12] base).
- `aa_ia_msb e = translation_size e.d128 e.tgx e.level + (contig ? contiguous_size … : 0)`.
- `aa_covers e va` — `va[55:ia_msb] == vatag[55:ia_msb]` (fixed-width shifts, as
  in `la_covers`).
- `aa_pa e va` — `stage_oa`: `oabase[55:ia_msb] @ va[ia_msb−1:0]`.
- `aa_refill`/`aa_flush`/`aa_lookup` — the hardware-walker refill and the TLBI
  invalidate (the `aa_flush` twin of `sfence_vma_va`/`mips_flush`/`la_flush`).

## Conformance oracle / plan

1. ~~Transcribe `ContiguousSize`/`TranslationSize`/`StageOA` into Sail and pin the
   size spectrum + OA by `vm_compute` vectors (4 KB/16 KB/64 KB × level × contig).~~
   **Done** — `aarch64_tlb.sail` + 35 vectors in `aarch64_tlb_proofs.v`.
2. ~~Prove the refill/flush/shootdown twins (`aa_flush_clears`,
   `aa_shootdown_correct`, …) over `AaEntry`, mirroring the MIPS/LoongArch
   proofs.~~ **Done** — `aa_refill_lookup_covers`, `aa_flush_clears`,
   `aa_unmap_without_flush_breaks_coherence`, `aa_refill_flush_composes`,
   `aa_shootdown_correct`, all axiom-free.
3. Differential-test against the vendored `sail-arm` model (the `TranslationSize`/
   `StageOA`/`ContiguousSize` fragments are already Sail, so the transcription is
   near-verbatim rather than a re-reading); the pgcl #9/#10 failure modes become
   the contpte/TLBI test vectors. **Remaining** — a full sail-arm differential
   equivalence (importing the vendored generated model and proving the fragments
   agree) is the next increment.

See `mmu-variants.md` (axis 1/2 table) and `failure-modes-pgcl.md` (#9, #10).

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
3. ~~Differential-test against the vendored `sail-arm` model...~~ **Done**
   (2026-08-17): `hardware/src/sail_arm_tlb.sail` extracts
   `ContiguousSize`/`TGxGranuleBits`/`TranslationSize` *verbatim* (modulo
   totality + the `SaTGx` rename) and is generated into `sail_arm_tlb.v`;
   `aarch64_sail_oracle.v` imports it (qualified) and proves the two
   transcriptions agree — `sa_tgx_granule_bits_conforms`,
   `sa_translation_size_conforms`, `sa_contiguous_size_conforms` (general, all
   d128/tgx/level) and `sa_ia_msb_conforms` (the StageOA `ia_msb` boundary),
   plus 4 StageOA `vm_compute` vectors pinning `baseaddress[55..ia_msb] @
   ia[ia_msb-1..0]` against the shift-based `aa_pa`.  The StageOA bit-slicing
   identity is now proved **generally** (`aa_stage_oa_spec`, 2026-08-17): the
   `uint`-distribution lemmas for `shiftr`/`shiftl`/`or_vec`/`zero_extend`/
   `subrange_vec_dec`/`concat` live in `mword_lemmas.v` (unfolding the
   transparent `MachineWord` instance to stdpp `bv_*`), removing the earlier
   abstract-`MachineWord` blocker (see loongarch-software-refill.md).

## pgcl #9/#10/#12 vectors (`aarch64_pgcl.v`, done 2026-08-17)

- **#9 contpte fold loses sub-page offset** — `test_vector_pgcl9_prefold_page0/1`
  pin the two distinct pre-fold 4 KB frames; `..._contig_fold_loses_offset` +
  `..._mismatch` pin that folding into a CONT entry re-points sub-page 1 at
  sub-page 0's frame + the offset (a wrong-page read, inv3 + M3).
- **#10 TLBI stride = PAGE** — `test_vector_pgcl10_page_stride_leaves_stale` pins
  that a single-page flush leaves the adjacent page's entry live, and
  `..._full_flush_clears` pins that the MMUPAGE-stride flush clears all of them
  (Property 1 / inv7).
- **#12 sparc64 TSB over-insertion (×c)** — `test_vector_pgcl12_single_demap`
  pins that a single insert + `aa_demap_one` removes the translation entirely,
  while `..._overinsert_stale` pins that a c=4 over-inserted TSB survives a
  one-slot demap (c−1 stale entries → lookup still hits a now-unmapped address);
  `..._overinsert_count` pins the exact c−1 = 3 stale entries (inv7: TLB ⊄
  mapping).

## Primary-source cross-check (Arm ARM DDI 0487, done 2026-08-17)

The sail-arm equivalence (#3) is a *secondary*-source check (against the vendored
ISA model's ASL).  The *primary* source is the **Arm Architecture Reference
Manual for A-profile (DDI 0487, issue M.c)** —
`~/Dokumente/DDI0487M_c_a-profile_architecture_reference_manual.pdf`.  Cross-checked
against the transcription with **all functions confirmed to match**:

- **Granule sizes** (`tgx_granule_bits` = 12/14/16) — 4 KB (D8-16: page resolved
  by a level-3 Page descriptor, `IA[11:0]→OA[11:0]`), 16 KB and 64 KB (D8-46).
- **Block/page sizes** (`translation_size` = `granulebits + (3−level)·(granulebits−descsizelog2)`) —
  matches **Table D8-17** (4 KB granule: L1 = 1 GB, L2 = 2 MB, L0 = 512 GB at
  DS=1) and **Table D8-46** (VMSAv9-128: 4 KB L2 = 1 MB, 16 KB L2 = 16 MB,
  64 KB L2 = 256 MB, …, L3 = the page size).
- **Contiguous bit** (`contiguous_size`) — matches **Table D8-104** (VMSAv8-64,
  `d128=0`) and **Table D8-105** (VMSAv9-128, `d128=1`) entry-for-entry: all 16
  (level, granule) rows agree (4 KB {1,2,3}→16; 16 KB {2,3}→{32,128};
  64 KB {2,3}→{32,32}; and the DS=1 table 4 KB {1,2,3}→{4,16,16}, 16 KB
  {1,2,3}→{4,16,64}, 64 KB {2,3}→{64,16}).  The reserved levels (D8.7.1 RHMQXG:
  CONT is RES0 in 4 KB L0@DS=1, 16 KB L1@DS=1, 64 KB L1) are the ones the
  transcription returns 0 for.
- **StageOA / `aa_pa`** — matches the “Final address” column of **Table D8-46**
  (`OAB[55:36]:IA[35:0]`, …, `OAB[55:12]:IA[11:0]`) and **Figure D8-3**: the
  high bits come from the descriptor OA base, the low `ia_msb` bits from the IA.
- **`aa_flush` (TLBI by VA)** — matches **C5.5.68** `TLBI VALE1/VALE2/VALE3`
  (“Invalidates … entries … that would be required to translate the specified
  VA”).  The model drops *every* covering entry (the whole Contiguous range),
  which is exactly what IVNXYF requires: “software is required to perform TLB
  maintenance on the entire address region that results from using the
  Contiguous bit” — the pgcl #10 failure mode.

One terminology correction recorded for rigour: the model’s `d128` flag is
**FEAT_D128** — the 128-bit (16-byte) translation-table descriptor, which the
manual names the **VMSAv9-128 translation system** (D8-46/D8-105).  It is *not*
`TCR_ELx.DS == 1`: DS is **FEAT_LPA2**, which extends the 4 KB/16 KB OA to 52
bits while keeping **8-byte descriptors** (the DS=1 columns of D8-16/17/26/27/
35/36).  The Sail comments’ “DS2/LPA2” shorthand is therefore imprecise; the
size machinery’s selector is descriptor width (D128), not DS.  Concretely,
`d128=0` = 8-byte descriptors (both DS=0 and DS=1-with-LPA2, so the D8.7.1 RHMQXG
“DS=1” RES0 notes — 4 KB L0, 16 KB L1, 64 KB L1 — all map to `d128=0` and return
0), and `d128=1` = FEAT_D128’s 16-byte descriptors (D8-46/D8-105).  This also
reconciles the apparent D8-104-vs-D8-105 tension: RHMQXG’s 16 KB L1 “DS=1 RES0”
is the 8-byte-descriptor case (`d128=0`), while D8-105’s 16 KB L1 = 4 entries is
the FEAT_D128 case (`d128=1`).

Not modelled (documented simplifications, out of scope for the TLB-encoding
layer): ASID/VMID/global/nXS matching in TLBI, translation-fault decode, stage-2
regimes, and `FEAT_XS`.  See `mmu-variants.md` and `failure-modes-pgcl.md`.

See `mmu-variants.md` (axis 1/2 table) and `failure-modes-pgcl.md` (#9, #10, #12).

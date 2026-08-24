# Custom RISC-V MMU Extension: Inverted Page Table with SLB + Residue Partitioning

## Summary

A custom RISC-V MMU extension (proposed satp modes 14 and 15) that replaces the
traditional hardware-walked radix tree with an **inverted (hashed) page table**,
a **POWER9-style SLB** segment cache, and **residue-based TLB partitioning**
covering **42 distinct translation sizes** (41 superpage sizes above the base
page) down to a 256 B base page.

The extension is modelled in Sail and proved in Rocq as part of the Tessera
hardware-model verification (§G1–G5 trust line).

## Motivation: Why 256 B Pages?

The VAX-11/780 (1978) had 512 B pages — already too small for early Unix, whose
4.1BSD kernel struggled with page-table fragmentation on VAX-11/750 systems with
only 1–2 MB of RAM.  The industry standardised on 4 KiB to balance TLB reach
against internal fragmentation, and there the matter rested.

**A 256 B page is half the VAX's**, and on a conventional radix-tree MMU it would
be catastrophic:

- 48-bit VA ÷ 256 B = 2^40 pages → 16-level radix tree (≈ zero TLB reach)
- Page-table memory overhead would exceed physical RAM
- TLB miss latency would be hundreds of cycles

**Page clustering changes the arithmetic.**  A cluster of `c = 16` 256 B hardware
pages forms one 4 KiB software allocation unit (the KAU).  A cluster of `c = 256`
forms a 64 KiB superpage.  With an **inverted page table**, the table is sized to
the number of *mappings* (not pages), so superpages **reduce** the table size
rather than requiring more PTEs.  The result is:

- **VAX-fine protection granularity** (256 B COW/sharing/dirty-tracking)
- **Large-page TLB reach** (64 KiB–256 MiB superpages, 42 translation sizes)
- **No radix-tree walk** (O(1) expected hash lookup)
- **Provable correctness** (the refill handler is verified, not trusted)

This is the "fine granularity *and* large-page efficiency" thesis that MIPS
PageGrain demo'd at 1 KiB; 256 B extends it further, recovering the VAX's
granularity without its pathologies.

### Why Existing Kernels Cannot Operate This MMU

No general-purpose OS in wide use could drive modes 14/15 in anything remotely
resembling its current form, for two compounding reasons.

**1. Explosive per-page metadata.** Almost every kernel allocates a per-page
descriptor (`struct page` in Linux, `mem_map[]`-equivalent elsewhere) sized to
the number of hardware pages.  At 256 B pages that metadata overhead is 16×
what it is at 4 KiB (and 8× the VAX's 512 B), for the *same* physical RAM.  The
metadata would rival or exceed the memory it tracks — exactly the
"Memory Wall" pathology Telix's coremapless design exists to eliminate.  A
kernel that keeps per-page descriptors cannot survive a 256 B base page
without a wholesale rewrite of its allocator, page cache, and reverse-mapping
structures.

**2. Radix-tree emulation is still unworkable.** The few kernels that might
attempt to dress the inverted page table up as a legacy radix-tree MMU (to
reuse existing walker/shootdown/reverse-map logic) hit the same wall from the
other side: a 256 B base page would need a radix tree of ~16 levels over a
64-bit VA (2^56 pages), whose page-table overhead dwarfs the mapped memory.
The dense 42-size spectrum cannot be flattened onto a fixed 4-level
walk without abandoning both the fine granularity and the inverted table's
size-∝-mappings property.

Both failures are specialisations of the same root cause: this MMU is only
drivable by a kernel whose memory management is built around extents and an
inverted structure from the start.  That is precisely what Telix provides
(morsel allocator, extent accounting, software-managed refill with a verified
handler), which is why the MMU is a Telix-specific research target rather than
a drop-in feature for existing kernels.

## Architecture

### Two New satp Modes

| satp mode | Description |
|-----------|-------------|
| 14 | Inverted page table (hash-based, no hardware walker) |
| 15 | Mode 14 + POWER9-style SLB segment cache |

Both modes use the same 64-bit VA space (no radix tree → no reason to limit to
48 bits).  The existing Sv39/Sv48/Sv57 modes are unaffected — modes 14/15 are
strictly additional.

### Address-Space Split and Page-Size Spectrum: g_n = K × 2^(W×n)

The 64-bit VA is split into a **14-bit segment ID** (16,384 segments) and a
50-bit segment offset.  The segment offset splits again into a **42-bit VPN**
and an **8-bit offset** within the minimum mapping granularity.

- **K** (Körnung, grain): 256 B (8 offset bits)
- **Segment**: 2^50 B = 1 PiB (14-bit segment ID)
- **W** (Sprungweite, jump increment): 1 bit
- **n** (size index): 0–41 → 42 distinct translation sizes

| n | Size | n | Size | n | Size |
|---|------|---|------|---|------|
| 0 | 256 B | 14 | 4 MiB | 28 | 64 GiB |
| 1 | 512 B | 15 | 8 MiB | 29 | 128 GiB |
| 2 | 1 KiB | 16 | 16 MiB | 30 | 256 GiB |
| 3 | 2 KiB | 17 | 32 MiB | 31 | 512 GiB |
| 4 | 4 KiB | 18 | 64 MiB | 32 | 1 TiB |
| 5 | 8 KiB | 19 | 128 MiB | 33 | 2 TiB |
| 6 | 16 KiB | 20 | 256 MiB | 34 | 4 TiB |
| 7 | 32 KiB | 21 | 512 MiB | 35 | 8 TiB |
| 8 | 64 KiB | 22 | 1 GiB | 36 | 16 TiB |
| 9 | 128 KiB | 23 | 2 GiB | 37 | 32 TiB |
| 10 | 256 KiB | 24 | 4 GiB | 38 | 64 TiB |
| 11 | 512 KiB | 25 | 8 GiB | 39 | 128 TiB |
| 12 | 1 MiB | 26 | 16 GiB | 40 | 256 TiB |
| 13 | 2 MiB | 27 | 32 GiB | 41 | 512 TiB |

The upper end of the spectrum is bounded by the segment size, not by the page
table format.  The `sp_vpn` (superpage VPN) is at most 42 bits, so the largest
representable translation is K × 2^41 = 2^49 bytes = 512 TiB (the whole 42-bit
VPN field, one bit above the 8-bit offset).  A segment (2^50 B) is exactly twice
the largest superpage, so no superpage can cross a segment boundary.

### Hash Function

```
sp_vpn = VA >> size_log2                         (superpage number)
partition = size_log2 mod 4                      (residue class)
phipt_hash(sp, part) = (sp_lo + sp_mid) + (part @ sp_hi)
```

The hash is **superpage-aware**: all VAs within a superpage hash to the same
slot (they share the same `sp_vpn`).  The partition stays constant across the
superpage.

### SLB (Segment Lookaside Buffer)

256-entry POWER9-style segment cache.  Each entry maps a 1 PiB virtual segment
(the 50-bit segment offset implied by the 14-bit segment ID) to its
segment-table pointer.  The SLB is probed first on TLB miss;
if it hits, the PHIPT search is restricted to the segment's translations
(avoiding a full table scan).

### TLB: Residue-Based Partitioning

Four TLB partitions, each caching translations for sizes where `size_log2 mod 4`
equals the partition index:

| Partition | Sizes (sample) |
|-----------|----------------|
| 0 | 256 B, 4 KiB, 64 KiB, 1 MiB, 16 MiB, 256 MiB, 4 GiB, … |
| 1 | 512 B, 8 KiB, 128 KiB, 2 MiB, 32 MiB, 512 MiB, 8 GiB, … |
| 2 | 1 KiB, 16 KiB, 256 KiB, 4 MiB, 64 MiB, 1 GiB, 16 GiB, … |
| 3 | 2 KiB, 32 KiB, 512 KiB, 8 MiB, 128 MiB, 2 GiB, 32 GiB, … |

**Why residue-based?**  Each partition spans the *full size range* — a partition-0
TLB can cache both a 256 B and a 64 GiB translation.  This preserves **TLB
expansibility**: the TLB adapts to the workload, unlike Intel's segregated
design (where L1 TLB is 4 KiB–only and can never cache a superpage).

### Translation Path

```
TLB → SLB → PHIPT (largest first, Zipf-optimised)
```

1. **TLB hit** (fast path): most-specific matching entry → PA
2. **SLB hit**: narrow PHIPT search to the segment
3. **SLB miss**: full PHIPT search, 42 sizes largest-first

With the Zipf distribution of superpage sizes (peak at the allocation unit Z,
short left tail, long right tail), the "largest first" strategy averages O(1)
probes.

## Partner Hashing (BKZ)

The inverted page table uses **partner hashing** (Bender-Kuszmaul-Zhou 2025),
which achieves load factor 1 with O(1) worst-case queries and O(1)
high-probability insertions/deletions.  The key insight: the permutation
ordering of entries encodes Θ(n log n) bits of metadata without extra storage.

For the inverted page table, this means:
- **No empty slots** (load factor 1: table size = number of mappings)
- **No rehashing** (dynamic resize, ±1 slot per insert/delete)
- **Metadata-free entries** (size, permissions encoded in the permutation)

See `doc/partner-hashing-inverted-pt.md` for the full adaptation analysis.

## Verification Status (Tessera)

| Artifact | File | Status |
|----------|------|--------|
| Sail model | `hardware/src/riscv_inverted_pt.sail` | ✅ typechecks |
| Rocq types | `hardware/rocq/riscv_inverted_pt_types.v` | ✅ generated (Sail → Rocq) |
| Rocq defs | `hardware/rocq/riscv_inverted_pt.v` | ✅ compiles |
| Hash consistency proofs | `hardware/rocq/riscv_inverted_pt_proofs.v` | ✅ 12 lemmas, axiom-free |
| Build integration | `hardware/rocq/build.sh` | ✅ wired (gen + compile + axiom check) |

### Proved Properties

1. **Hash determinism**: same inputs → same hash (`eq_vec` level)
2. **Superpage consistency**: VAs in same superpage hash identically
3. **Partition well-definedness**: partition = `size_log2 mod 4`
4. **Coverage agreement**: TLB entry covering VA → hash matches
5. **Concrete test vectors**: 4 KB and 64 KB hash consistency, sp_vpn
   agreement/difference, partition identity

### Remaining Proof Obligations

- **Shootdown coherence**: `phi_tlb_flush` + `phipt_invalidate` restores
  TLB ⊆ PHIPT (the Tessera §4 crux, replayable from `coherence.v`)
- **SLB hit-rate bounds**: with realistic workloads and PHIPT sizing
- **Concurrent weak-memory lift** (gpfsl): the IPI-based shootdown over
  the inverted page table
- **QEMU simulation branch**: satp modes 14/15 for testing

## Relationship to Prior Work

- **VAX-11 (512 B pages)**: the 256 B base page is half the VAX's; clustering
  solves the TLB-reach problem that plagued early BSD
- **MIPS PageGrain (1 KiB pages)**: telix's existing MIPS target; the 256 B
  design extends the same principle further
- **POWER HPT**: the SLB + inverted-table architecture mirrors POWER's
  segment → HPT path; partner hashing improves on POWER's set-associative PTEG
- **SPARC TSB**: the software-managed TSB with per-entry size encoding is the
  architectural precedent for multi-size hash-table TTW
- **BKZ (2025)**: partner hashing provides the load-factor-1 guarantee that
  makes an always-full inverted table practical

## References

1. Bender, Kuszmaul, Zhou. *Optimal Non-Oblivious Open Addressing.*
   arXiv:2503.13628, 2025.
2. IBM. *Power ISA Version 3.1C.* Hash Page Table specification, 2023.
3. Sun Microsystems. *UltraSPARC Architecture 2007.* TSB specification.
4. MIPS Technologies. *MIPS64 Privileged Resource Architecture.*
   MD00091, Rev. 6.03.  PageGrain (Config3.SP + PageGrain.ESP).
5. Tessera. `doc/mmu-variants.md`, `doc/partner-hashing-inverted-pt.md`.
6. Digital Equipment Corporation. *VAX Architecture Handbook*, 1981.

---

*This document describes the custom RISC-V MMU extension as modelled in Tessera.
The extension is a research prototype; hardware implementation would require
RISC-V Foundation ratification of the new satp encodings and the inverted-page-table
ISA extension.*
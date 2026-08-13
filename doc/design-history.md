# Design history — where the clustering came from

This note records the provenance of the technique Tessera formalizes, so the model's
abstractions (KAU, MMG, cluster factor `c`, "invisible to correctness") can be read
against the lineage that motivated them.

## The technique: ABI-compatible page clustering (Dickins)

Tessera's object is a *clustered* VMM: a kernel allocation unit (KAU) of size
`P = c·M` above the minimum mapping granularity (MMG) `M`, with translation state
tracked at the `M` granularity (a vector of `c` PTEs per KAU) and superpaging as a
single TLB entry spanning a KAU — `tessera-verification-kickoff.md` §0.

That idea descends from **Dickins' ABI-compatible page clustering**. The discipline
— cluster the allocation unit, track at the finer granularity, and keep the
clustering invisible to the application binary interface — is the same contract the
brief states as a refinement: *"clustering and superpaging must be invisible to
correctness"* (the top-level theorem).

## The 2003 forward port and the 64 GiB 32-bit x86 boot

The project's author, under a former name, wrote the **2003 forward port** of
Dickins' clustering, and that port carried the **first public boot of Linux on
64 GiB of RAM on 32-bit x86**. The clustering earned its keep there precisely
because a 32-bit kernel cannot afford the per-page bookkeeping that 4 KiB
granularity across 64 GiB imposes: the 4 GiB kernel address space cannot carry a
`mem_map` descriptor array and page tables for the ~16M base pages (64 GiB / 4 KiB)
without crowding out the kernel itself. Clustering the allocation unit — and its
`struct page` bookkeeping — is what made 64 GiB addressable and manageable at all.

This is the **existence proof** the whole line rests on: the technique shipped on
real hardware, at a scale where the unclustered alternative does not fit.

## The sibling: arbitrary-sized CPU bitmaps (2003)

The same author, the same year, integrated **arbitrary-sized CPU bitmaps** into
Linux. This is the same shape of idea Tessera preserves as a *parameter*: a
power-of-two assumption is an implementation convenience, not a law — exactly the
observation behind telix's `PAGE_MMUSHIFT` as a kernel command-line option and the
odd cluster factors the model must tolerate. It is a natural second Layer-I target
beside `ExtentMap` / `BTree` / `Pte`.

## Mapping to the model

| 2003 lineage | Tessera |
|---|---|
| cluster the allocation unit | KAU, size `P = c·M` (brief §0) |
| track at the finer granularity | the `c`-vector of `M`-grained PTEs per KAU |
| superpage = one TLB entry spanning the KAU | promotion (`intra-kau-tiling.md`) |
| clustering invisible to the ABI | the top-level refinement theorem |
| 32-bit x86 can't afford per-4-KiB tracking | the `c = 64` sweet spot (`clustering-rationale.md`) |

## To confirm (author's to fill in)

The specific historical parameterization of the 2003 instance (its `M`, cluster
factor `c`, and the exact `struct page`/bitmap layout), the full Dickins reference,
and the author's former name are the author's to supply — this note deliberately
records the lineage and the existence proof without guessing at those specifics.

# pgcl — memory-management failure-mode catalog

**Purpose.** A catalog of MM bugs that actually occurred during pgcl development
(the Linux page-clustering / superpage port), mapped to the Tessera invariants
(see `tessera-verification-kickoff.md`). This is the empirical threat model: it
tells the verification *what it must prove cannot happen*, and which invariants
carry the real-world risk. Mined read-only from `~/src/pgcl/` debugging artifacts
(commit messages, ablation/bisect/dangle `.out` logs, `dmap-ptetable-hunt.md`,
`bug6-instrumentation.patch`), the `~/src/linux-pgcl-mc` git history (~170 PGCL
commits on a v7.1 base), and the Claude session transcript.

**Vocabulary.** pgcl `MMUPAGE_SIZE` = Tessera **M**; `PAGE_SIZE = MMUPAGE_SIZE <<
PAGE_MMUSHIFT` = Tessera **P** (the KAU); `PAGE_MMUCOUNT` = cluster factor **c**;
one `struct page` per KAU; the **c** PTEs per KAU are the brief's PTE-vector.

**The structural crux behind almost every bug.** Under pgcl `pte_pfn()` drops the
sub-page bits, so **all c sub-PTEs of one KAU resolve to the same `struct
page`/folio**. Any code that iterated `page + i` or counted in `PAGE_SIZE` units
instead of `MMUPAGE_SIZE`/per-PTE units corrupted refcount, mapcount, RSS, or
TLB/cache state. This is exactly the Layer-A "PTE-vector vs single-entry"
coherence the brief calls the heart of the model.

## A) Catalog

| # | Title | Symptom | Root cause | Subsystem / commit | Category | Tessera caught-by |
|---|---|---|---|---|---|---|
| 1 | **#143 file-folio rmap under/over-remove → page-cache corruption** | mapcount underflow `refcount:-10 mapcount:-15`; freed-while-mapped folio reused; dangling user PTE | rmap remove side decrements more than add side when a KAU's sub-PTEs are gapped/migrated; folio freed while still mapped, then reused | mm/rmap, zap/COW batch (`9567ec305d3b`, `5e2620b0e2f6`) | refcount + partial-population + UAF | **inv2** (PTE-vector integrity), **inv6** (COW), Layer A; breaks M3 refinement |
| 2 | **`page+i` sub-page iteration corrupts neighbors** | "Bad page state"; refcount/mapcount on *adjacent* memmap pages corrupted | copy/zap walked `page+i`, striding *other KAUs'* struct pages | mm/memory.c `2af00f068f00` | refcount / inv2 | **inv2**; M2 map/unmap postcondition |
| 3 | **try_to_unmap_one early-exit drops PTEs after partial yield** | refcount leak; TLB entries leaked; folio looks unmapped with live sub-PTEs | `batch_kpages==folio_nr_pages` fired on first partial yield; PTEs 8..15 of a gapped KAU never unmapped | mm/rmap `2e4c4283d8b7` | partial-population + lost-flush + refcount | **inv2 + inv7 + Property 1**; M2 unmap |
| 4 | **try_to_unmap/migrate stale `nr_pages` across PVMW iterations** | refcount/mapcount/RSS corruption with device-exclusive PTE after a batched present batch | function-scope `nr_pages` reused on a different-path iteration | mm/rmap, mm/migrate `e38e7ecb65eb` | refcount / inv2 | **inv2**; M2 |
| 5 | **rmap event-count convention split (Option A vs B)** | `Bad page state … mapcount:-15` (ppc64 DEBUG_VM); 9:1 REM:ADD; anon recycled as SHMEM | fault path emitted 1 rmap event/KAU; zap loop emitted c/KAU → mapcount underflow by c−1 | mm/memory, mm/rmap, mm/migrate `5e2620b0e2f6`, `886d1ae96066` | refcount/mapcount | **inv2, inv5**; M2 |
| 6 | **migration restore/remove asymmetry → unreclaimable folio** | folio `_mapcount` stuck at c after a migration round-trip; never reaches 0 | `remove_migration_pte` added rmap c/KAU while teardown removed 1/KAU; walker didn't batch migration entries | mm/migrate, page_vma_mapped `146ab21a5d03`, `5aa9ff637c3f` | migration + refcount | **inv2**; M2 (migrate/merge) |
| 7 | **THP split leaves phantom `_mapcount=0` → free-while-mapped UAF** | `Bad rss-counter state`; sub-folio self-reports mapped after split; `folio_put` frees a still-mapped page | bulk-init of all c sub-page mapcounts to 0, but partial fault installs 1 PTE; split doesn't reset head | mm/huge_memory `c30352064c4c`, `7dcee907e3b5`, `c7221b452105` | huge-page split error + UAF + partial-population | **inv4** (consistent split/merge), **inv2**; M2 split (brief's named "split/fold" core) |
| 8 | **`__split_huge_zero_page_pmd` wrong loop bound → RSS leak** | unbalanced RSS increments; RSS leaks ppc64/x86 | iterated `HPAGE_PMD_NR` × `PAGE_SIZE` stride instead of `HPAGE_PMD_MMUNR` × `M`; left c−2/c slots `pte_none` | mm/huge_memory `8619b76a6f2c` | split error + partial-population | **inv4**; M2 demote/split |
| 9 | **arm64 contpte fold loses sub-page offset → wrong-page reads** | `cow_just_fork`/`cow_mprotect_race` SEGV pc=0/lr=0; reads return wrong sub-pages | `contpte_convert` rebuilt PTE at sub-page 0; CONT ranges silently re-pointed to sub-pages 0..c−1 | arch/arm64 contpte `036a0e39c6be` | promotion/fold error | **inv3** (superpage uniformity), **inv1**; M3 refinement |
| 10 | **TLB flush stride = PAGE not MMUPAGE → c−1/c entries stale** | stale TLB; MREMAP_DONTUNMAP returns old data; ~41 LTP fork SEGVs (ARM32) | INVLPG/tlbi stepped `PAGE_SIZE`, flushing 1 in c hardware entries | x86/arm64/ppc/arm32 `b4f79cac8bde`, `7d53be535bb1` | **stale-TLB / lost-flush** | **inv7 + Property 1** — canonical forgotten flush; M2 unmap/mprotect |
| 11 | **vmap CONT huge-PTE from truncated pfn → SMP IPI loss / wrong MMIO** | aarch64 SMP hang; GICC mapped onto GICD; IPIs dropped | `pfn_pte(paddr>>PAGE_SHIFT)` dropped sub-PAGE bits at the huge-PTE branch | mm/vmalloc, arm64 `fd4ad3a67b31` | alignment/overlap (wrong physical) | **inv1**; M2 map |
| 12 | **sparc64 TSB over-insertion (×c) → silent data loss** | COW writes land in wrong pages; demand-zero faults suppressed | `update_mmu_cache_range` ×`PAGE_MMUCOUNT` though callers pass PTE count → c× bogus entries | arch/sparc64 `da3fc3e93bf0`; dual: missing inserts `ea353c69335c` | stale-TLB / over-broad cache | **inv7** (TLB ⊄ mapping), **Property 1**; M2 |
| 13 | **set_ptes nr double-expansion → PCP freelist corruption** | arm64 `POISON_FREE in __rmqueue_pcplist`; UAF | THP-split passed KAU count, `folio_pte_batch` returned PTE count, arch `set_ptes` multiplied again | pgtable, arch set_ptes `e9c29ad5b35d`, `263c4dc62885` | refcount / UAF | **inv2**; M2 |
| 14 | **filemap_map_pages fault-around crosses PMD → phantom PTEs leaked** | phantom PTEs in a *neighbor PMD's* table; table freed while populated | `pte_index(addr)` ignores PMD bits; fault-around spanning PMDs wrote `set_ptes` past the table | mm/filemap `a4163836cf92` | overlap + partial-population + UAF | **inv1** (disjoint/aligned), **inv4**; M2 |
| 15 | **relocate_vma_down breaks vm_pgoff↔vm_start sub-page assumption** | COW reads user stack as a PTE → garbage PFN → panic; or wrong-sub-page copy → SIGSEGV rip=0 | 5 sites derived sub-page index from `vm_pgoff`; stack relocation keeps original phys alignment; `vmf->pte - sub` underran the table | mm/memory.c `cd7ebf833e33` | COW + alignment + OOB | **inv1, inv6**; M2 COW-break, M3 |
| 16 | **L1TF protnone re-invert omitted in 4K-leaf loop → reserved-bit #PF** | "corrupt free page"; reserved-bit #PF; defeated boot for many sessions | per-sub-page `__change_page_attr` loop un-inverted old PTE but never re-inverted new prot | arch/x86 set_memory.c (`106-commit-msg.txt`) | PTE bit-encoding | **Outside model** — HW PTE encoding/L1TF; Layer-I at most; trusted-hardware boundary |
| 17 | **iounmap frees PAGE-rounded memtype range → leak + warn storm** | `x86/PAT: freeing invalid memtype`; rbtree node leaked; soft-lockup | reserve MMUPAGE-granular but free used `get_vm_area_size()` (rounded to KAU) | arch/x86 PAT (`129-commit-msg.txt`) | alignment + metadata leak | **inv1** (alignment); partly outside core mapping model |
| 18 | **DRM/GEM sized in KAU but faulted in MMUPAGE (3 bugs)** | `BUG_ON(size & (PAGE_SIZE-1))`; GEM mmap mis-mapped (c−1/c wrong); SIGBUS at offset ≥ P | GEM accounted per-KAU but vm_pgoff/fault offset per-M | drm/gem, drm/shmem (`144-*.txt`) | alignment + overlap | **inv1, inv2**; driver layer (outside core VMM) |
| 19 | **swap clustering / encoding: per-sub-page slots, shift mismatch** | swap-in data loss / list corruption per-KAU; ppc/sparc swap PTE fields mis-positioned | order-0 folios aren't compound under pgcl → each sub-page owns its swap slot; `__swp_offset` used `PAGE_SHIFT`; swap-in clustering `#if 0` | mm/swap_state, arch swap macros `fe5a73f74de7`, `105be1b39c96`, `a08c960447cc` | partial-population + encoding | **inv2**; M2 ("partially populated" KAU) |
| 20 | **dirty/clean & referenced batching peeks only first sub-PTE** | writeback leaves a writable sub-PTE modifiable (corruption); referenced walker desyncs PTE vs address by ×c | `page_vma_mkclean`/`folio_referenced` early-skip checked only PTE 0 of the KAU | mm/rmap `e755bf47e2e0`, `3fc2b7084a2a` | dirty/referenced aggregation + lost-flush | **inv5** (OR over PTE vector) + **inv7/Property 1**; M2 |

Lower-novelty also seen: `pgcl_page_folio` partial conversion → double-free (`545187cf3819`); `__split_folio_to_order` reset un-gated at shift 0 → free-while-mapped (`c7221b452105`); `unmap_mapping_range_tree` unit mix → zap past vm_end (`92f949830f3e`); slub `oo_objects` overflow (`d3f1e24dbb3c`, `7532dbf70d5f`). The `dmap-ptetable-hunt.md` audit concludes #106's *consumer* is a clean direct-map PTE table corrupted by the wider rmap-lifetime bug class (#1/#7) — a refcount/lifetime UAF, not an encoding defect.

## B) Ranked priorities for the proof

1. **rmap event-count / mapcount aggregation over a PTE vector** (#1,#2,#5,#6). Largest cluster (744 "mapcount underflow" transcript hits). Wrong per-KAU aggregation of the c per-M mapcounts → free-while-mapped → UAF / page-cache corruption. This *is* inv2+inv5 and is the project's central novelty.
2. **Free-while-mapped via split/fold leaving phantom mappings** (#7,#8,#9). Superpage/huge-page split and contpte fold that don't restore per-M state — inv3/inv4, the brief's named "split/fold" heart.
3. **Stale-TLB from PAGE-stride flush** (#10,#12). The textbook insufficient flush the brief elevates to Property 1 + inv7. Flushing 1-of-c entries is exactly what a TLB-less proof cannot see.
4. **Partial-population & gapped-KAU unmap** (#3,#14,#19). A KAU with some sub-M pages present and some absent — the brief's explicit "partially populated" state.
5. **PTE-vector vs single-entry coherence in install paths** (#11,#13,#15). Truncated/double-expanded PTE counts and wrong sub-page offset — what M3 refinement must forbid.

## C) Coverage vs. the brief's scope

- **In scope for sequential M1–M3 (the large majority):** all rmap-aggregation bugs (#1–#8,#20) are sequential miscounts over the extent + PTE-vector (inv2/inv5/inv4); the fold/split geometry (#7–#9,#14,#15) is inv1/inv3/inv4 + the M3 refinement (#9 "reads wrong sub-page" is the cleanest M3 counterexample); the flush bugs (#10,#12,#20) are the **flagship Property-1 cases** — model the TLB/TSB as explicit state with stride = M, and a PAGE-stride flush *fails to verify*.
- **Inherently Property 2 (deferred / litmus):** none of the *fixed* bugs is a proven weak-memory shootdown-ordering defect. SMP pressure was a *trigger* (the #143 repro needs SMP8 + fork + COW), but each underlying defect was a sequential miscount or a local missing flush — strongly validating the brief's decision to defer Property 2 to a standalone litmus check.
- **Outside the model (trusted-HW / Layer-I / driver):** #16 (L1TF PTE bit-encoding), #17 (PAT rbtree leak), slub overflow, #18 (DRM/GEM granularity).

## D) The clustering-specific bugs (the heart of what Tessera models)

- **Split → phantom/leaked sub-mappings:** #7, #8. Split must reset every post-split sub-slot to "unmapped" and restore only where a real PTE exists (inv4 + the COW/demotion precondition the brief asks to be made explicit); #c7221b452105 shows *over*-resetting a still-mapped head is equally fatal.
- **Promotion/fold preserving per-M offset:** #9 (inv3 + refinement) — folding c PTEs into a superpage must keep each sub-M page pointing at its own M-frame.
- **TLB/TSB over-insertion during promotion:** #12 — bogus entries with no backing PTE violate inv7 (TLB ⊆ mapping).
- **PTE-vector vs single-entry, the recurring spine:** #1,#2,#5,#13 — because all c sub-PTEs share one `struct page`, every op must treat the per-KAU answer (refcount, mapcount, dirty, referenced) as the correct aggregation over the c-vector (inv2, inv5). The Option-A/B fracture (#5) is the purest case.
- **Partially-populated KAU:** #3,#14,#19 — gapped sub-PTEs within a KAU; the proof must let a KAU be a *partial* map over its c slots and still refine Layer S.

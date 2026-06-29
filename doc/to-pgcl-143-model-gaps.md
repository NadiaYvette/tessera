# To pgcl — #143 model-incompleteness survey + deferred-work re-enablement plan

Four parallel audits (THP/khugepaged conversion · split-PTL coherence · heterogeneous/partial
mapping · broad 1-PTE sweep) + the seed-localizer boot (0 `PGCL143-INV`) + the mmu_gather deferred-rmap
read. Goal Nadia set: line up review-readiness next steps, especially **re-enabling the deferred work we
disabled to stabilize** (delayed rmap removal, deferred TLB/batch). Heterogeneous superpages confirmed a
non-issue (nothing creates them; the model assumes MMUPAGE PTEs map one kernel allocation unit, ARM contig
aside) — dropped from scope.

## A. Live crash root — what's now ruled OUT, and where it actually points

Seed-localizer (`-pgcl4seed`, inv at every fault/fork/fault-around/reclaim/migrate-restore) fired **zero**
with the instrument verified linked (`nm`) and `present_at` validated against the live clamp scanner. So:

- **fault / fork / fault-around / reclaim / migrate-restore: balanced** (empirical, 0 INV).
- **khugepaged collapse: GATED DEAD** — `collapse_file`, `try_collapse_pte_mapped_thp`, `collapse_scan_pmd`
  all `#if PAGE_MMUSHIFT return SCAN_FAIL` at entry (khugepaged.c:1267, 1529, 1914). The 16× addr/pte
  desyncs are real but **unreachable**. ⇒ the `transparent_hugepage=never` A/B is **expected negative**
  (collapse is already off); not worth a boot.
- **THP split: REFUTED** — `PGCL143-SPLIT-RESET=0` (probe verified compiled, 0 THP splits). Audit-1's
  "split-reset is the culprit" rests on the in-tree *hypothesis* comment, not data — same trap, declined.
- **split PTL: coherent** (see §E).

**So the origin is not any single-op miscount** (every per-op path is MMUPAGE-balanced). It is an **emergent
cross-mm effect on shared FILE folios** — exactly the workload: every comm (element-desktop, V8Worker,
signal) shares the same Electron/V8/glibc `.so` text, so these order-0 FILE clusters are mapped in *many*
mms. Two concrete cross-mm hazards the audits surfaced:

1. **The clamp itself is single-mm (Audit-3 B1).** `present_here` counts only the *current* page table;
   the clamp `atomic_set(_mapcount, present_here-1)` (memory.c:1942, 2088) discards the other mms'
   contributions when it fires on a shared folio — under-restoring it and **perpetuating** the deficit
   (the clamp1 "feedback loop"). The invariant `mc+1 >= present_here(one mm)` is only sound single-mm;
   the only cross-mm-safe local signal is the true underflow `_mapcount < -1`.
2. **Deferred refcount vs immediate mapcount (Audit-3 #2, the 1 PIN-FAIL).** mapcount is removed under PTL
   immediately, but the folio ref is dropped via the mmu_gather batch / `folios_put` — a cross-mm aggregate
   free can hit refcount 0 while another mm still maps the cluster (dual_lockstep over-drop). This is the
   `SharingRace.Aggregate` territory.

**Next instrument (v2):** stop using single-mm `present_here`. Track the folio's **total present across
ALL mms** (an rmap walk, or the existing `_mapcount` vs a cross-mm scan) and assert `mc == Σ present` at
the clamp/atomic_set sites and at the deferred-free boundary. The origin is where the *global* identity
first breaks — which single-mm instrumentation structurally cannot see.

## B. Deferred-work re-enablement (Nadia's review directive) — the infra already exists

`delay_rmap` is forced off only by `if (!PAGE_MMUSHIFT && tlb_delay_rmap(tlb))` (memory.c:1894). The
reason is **instrumentation, not correctness**: immediate removal lets `present_here` scan live PTEs (the
deferred flush runs after the PTEs are gone). The pgcl tree **already built the correctness mechanism** to
make deferral safe:

- `__tlb_remove_folio_pages_size` (mmu_gather.c:196): on `delay_rmap`, `pgcl143_pending_inc(pfn)` **holds
  the cluster across the deferred window** — "folios_put_refs refuses to free a cluster with a pending
  removal, so a cross-mm aggregate free cannot drop it before tlb_flush_rmap_batch runs (the
  deferred-rmap UAF)."
- `tlb_flush_rmap_batch` (mmu_gather.c:74-82): runs the deferred `folio_remove_rmap_ptes(folio, page,
  nr_pages, vma)` with `nr_pages` decoded from the `ENCODED_PAGE_BIT_NR_PAGES_NEXT` batch entry (correct
  sub-PTE count), then `pgcl143_pending_dec(pfn)` releases the hold.

**Re-enable plan (the steps to drop the band-aid):**
1. Remove the `!PAGE_MMUSHIFT` guard at memory.c:1894 → allow `delay_rmap=true` under PGCL.
2. Drop the debug CLAMP + `present_here` scan from the zap (they require live PTEs and are debug-only; the
   shipping kernel carries no `pgcl143_*` instrumentation). The deferred path then needs no live-PTE scan.
3. Verify the `pending_inc/dec` hold is balanced (inc at queue, dec at flush, and at every early-return /
   force-flush path) and that the encoded `nr_pages` is the cluster sub-PTE count, not a kernel-page count.
4. Confirm the same for the **deferred batch free** (`__tlb_batch_free_encoded_pages`) — it already decodes
   `nr_pages` per entry (mmu_gather.c:130-148); audit that `folio_ref_sub`/`folios_put` use the same unit.
5. The residual cross-mm UAF (the 1 PIN-FAIL on the *immediate* path) is the SAME `SharingRace.Aggregate`
   gap as §A.2 — fixing it (hold a ref before the cross-mm free, never resurrect) closes both the deferred
   and immediate windows. This is the one piece of real new work; the rest is removing scaffolding.

So: re-enabling deferred rmap is **mostly deleting the stabilization band-aid**, once §A's cross-mm
accounting is correct. Upstream will want this — a kernel that disables `delay_rmap` is a non-starter.

## C. Model-gaps for review (broad sweep, Audit-4) — ranked

- **madvise.c:524, 752 + mlock.c:349** — `folio_mapcount(folio) != folio_nr_pages(folio)` (missing
  `* PAGE_MMUCOUNT`). A fully-mapped cluster reads mapcount 16 vs nr_pages 1 → **MADV_PAGEOUT / COLD /
  FREE and mlock/munlock silently no-op on the common fully-mapped folio.** Functional, safe (always errs
  toward "skip"), high exposure. FIX: scale by `PAGE_MMUCOUNT` (smaps already does `DIV_ROUND_UP(mapcount,
  PAGE_MMUCOUNT)`).
- **pagewalk.c:816 `walk_page_mapping`** — mixes PAGE-unit cache index with MMUPAGE-unit pgoff →
  write-protects/dirty-clears the **wrong PTE range**. Corruption-class but **low exposure** (DAX/PFNMAP
  dirty-tracking; only correct today when `vm_pgoff==0`). FIX: MMUPAGE_SHIFT + the mm.h pgoff helpers.
- **task_mmu.c (pagemap:2168, numa_maps:3249, smaps PSS:982)** — wrong-stats only (THP/hugetlb-gated).
- **x86 PTE-pack wiring** — the per-sub-table ptlock array (`pte_pack_index`) is armed **only on mips**;
  x86 leaves `PTE_PACK_NR=1` and pays ~16× page-table memory (one 64K page per 4K table). Latent: packing
  x86 later *without* defining `PTE_PACK_ORDER` self-deadlocks `copy_pte_range`. FIX: `BUILD_BUG_ON(
  PTE_PACK_NR < PAGE_MMUCOUNT)` guard before any x86 packing.

## D. Verified SOLID (no action) — useful for the review narrative

Add/remove/dup/migrate/reclaim all MMUPAGE-symmetric incl. partial/gapped clusters; rss/refcount/mapcount
move in the same unit; the straddle case (misaligned cluster crossing a PMD edge) is handled on install,
zap, fork, COW, swap, and the PVMW walk (each side either anchors to the in-table PAGE window `pte - sub`
with `t<0||t>=PTRS_PER_PTE` guards, or stops at the PMD boundary and re-locks). GUP pins per sub-PTE.
mprotect/mremap/mincore/gup/swap/userfaultfd cleanly converted.

## E. Split page-table locks — answer to "what on Earth is going on"

A PTE table is 4K (one MMUPAGE) holding 512 MMUPAGE-granular entries = one PMD's 2M, but `PAGE_SIZE` is
64K, so up to 16 sub-tables pack into one 64K page-table page. The port adds an **array of `PTE_PACK_NR`
ptlocks per ptdesc**, indexed by `pte_pack_index(addr) = (addr>>MMUPAGE_SHIFT)&(PTE_PACK_NR-1)`
(mm.h:3768-3815) — each 4K sub-table gets its own lock, preventing the `copy_pte_range` self-deadlock two
sub-tables sharing a ptdesc would cause. `PAGE_MMUCOUNT (16) | PTRS_PER_PTE (512)` guarantees a PAGE-aligned
cluster never straddles. **The model is coherent.** Caveat: the packing is only wired on mips
(`arch/mips/.../page.h`); x86 runs unpacked (see §C). Verdict: the lock design is sound; the "huh?" is that
on x86 the clever part is dormant and you're paying memory for it.

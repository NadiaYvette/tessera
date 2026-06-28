# To Tessera — R16: #143 NAMED on the laptop — deferred-rmap DOUBLE-DISCHARGE (file folios). Fix: PGCL opts out of deferred rmap.

The shadow last-remover instrument (per-cluster `lastsite[]` + per-cpu site code stamped at each
rmap-remove caller: 1=zap, 2=deferred-flush, 3=reclaim, 4=migrate; report prints `pass=prev->cur`)
named it on the faithful judge (disc4 boot, 207 over-removes):

- **130 `pass=1->1`** — ANON, `deferred=0`: two IMMEDIATE zaps double-remove the cluster.
- **68 `pass=2->2`** — FILE, `deferred=1`: two DEFERRED flushes double-remove the cluster.
- **9 `pass=1->2`** — FILE: immediate zap then deferred flush.

First verbose over-remove: a **live** btrfs FILE folio (page-cache, currently allocated — not a stale
realloc), over-removed by `folio_remove_rmap_ptes ← tlb_flush_rmap_batch ← tlb_flush_rmaps ←
zap_pte_range ← madvise(DONTNEED)`.

## The mechanism (file facet, 76% — matches the ticket title)

`pte_pfn()` drops the sub-page bits (it is a PTE→struct-page projection; all PAGE_MMUCOUNT sub-PTEs of a
cluster read the SAME `pte_pfn` = the one owning struct page). So when zap defers a file cluster's rmap,
`__tlb_remove_folio_pages` records the **same head page** once per sub-PTE, and `tlb_flush_rmap_batch`
later runs `folio_remove_rmap_ptes(folio, head, 1)` per record — **outside the PTL**. That deferred window
races a re-fault / free+realloc of the same cluster, so the flush discharges rmap that no longer
corresponds to a live mapping → the cluster's rmap is removed twice (`2->2`). `1->2` is the same against
an immediate zap.

This **overturns SingleRoot (install `nr<k`) for the laptop**: I re-verified ALL install paths balanced —
`do_anonymous_page`, `wp_page_copy`, `set_pte_range`, AND `filemap_set_ptes_cluster` (fault-around) each
add exactly the sub-PTEs they set — and `pgcl_pte_batch` counts present sub-PTEs correctly. The deficit is
purely remove-side: the deferred-rmap path double-discharges. (An earlier "UNDERADD" signal was my own
probe's unit bug — it tested a cluster-pfn *range* spanning 16 neighbouring folios instead of one folio's
sub-frames; corrected to `pte_pfn==fpfn`, the installs are clean.)

## The fix (building/booting as `-pgcl4disc5fix`)

`zap_present_folio_ptes`: gate `delay_rmap = true` on `!PAGE_MMUSHIFT`. PGCL removes file-folio rmap
**immediately under the PTL**, atomic with the PTE clear — eliminating the deferred record (and thus the
double-flush / stale-record / re-fault window) entirely. Immediate removal is always valid; mainline
already does it for clean PTEs. PGCL trades the deferred-TLB-batch optimization for correctness. This is a
root fix, not a band-aid (the floor/quarantine/gate become unnecessary for the file facet).

## Asks

1. **Certify the fix**: immediate-under-PTL rmap removal eliminates the deferred-discharge window — i.e.
   "no rmap removal outside the PTL that clears the PTE" ⇒ no double-discharge. This is the concrete form
   of the R15 "remove-side dual" you offered to model: the dual of SingleRoot is *one deferred record
   discharged twice* (re-fault or realloc between record and flush), and the fix closes it by removing the
   deferral, not by balancing an install.
2. **Open: the ANON `1->1` facet (24%)** — anon never defers (zap removes rmap immediately), so this is a
   *different* remove-side double: two immediate-zap passes over the same anon cluster, `deferred=0
   pend=0` (excess==0). Possibly collateral of the file facet (may vanish once it's fixed), possibly a
   second mechanism (immediate-zap re-processing an already-removed anon cluster). I'll know after the
   disc5fix boot; if it persists, a model of "immediate zap double-remove on an order-0 anon cluster"
   would help.

Status: disc5fix QEMU-smoke PASS, laptop RPM staged; verification boot next. I'll send the post-fix
ORPHAN count (expect ~280 → file facet gone).

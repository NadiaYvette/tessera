# pgcl #143 CBMC findings — integrated into Tessera

Integration of the pgcl-side CBMC bug-hunt of **#143** (the file-folio rmap over-drop →
page-cache corruption) into the Tessera verification effort. Source of truth on the pgcl
side: `pgcl:rmap-ab/formal/{TESSERA-BRIDGE,EMPIRICAL}.md` and the models under
`rmap-ab/formal/`. This file is the Tessera-side record + reciprocation.

## What pgcl's CBMC + audit established (the refinement of catalogue #1)

Catalogue item #1 (`failure-modes-pgcl.md`) originally read: *"rmap remove side decrements
more than add side when a KAU's sub-PTEs are gapped/migrated."* The hunt **refined** this:

- An **exhaustive code audit** proved every in-tree remove path (`try_to_unmap_one`,
  `try_to_migrate_one`↔`remove_migration_pte`, `zap_present_ptes`) and every install path
  drives *clear == rmap-drop == ref-drop* from one per-PTL-section count. **There is no
  intra-function / per-section over-drop** — "remove > add per section" does **not** occur.
- A CBMC model showed an over-drop is *sufficient* for the freed-while-mapped end-state but
  is *not present* in the section math. So the residual #143 bug is one of:
  1. **batch-count over-count** — `page_vma_mapped_walk`'s `nr_mmupages` groups sub-PTEs by
     `pte_pfn` only; if it ever spans two same-pfn mappings or the vsub≠psub file case, it
     counts past the one mapping → over-drop. **inv2** (PTE-vector integrity); home
     `Pte.lean` + the walker.
  2. **cross-mm aggregate-free** — each mm balanced, but the section dropping the last
     *aggregate* ref frees while another mm's sub-PTEs are present, with no `folio_mapped()`
     guard. **Property 2** + the Backing refcount discipline (`Sharing.lean`/`Teardown.lean`
     category G).
  3. **out-of-protocol** — TLB coverage (inv7/Property 1, weight low, QEMU did not confirm)
     or page-cache/truncate units (inv1/inv2 + Backing).

**Sharpened obligation:** Property 2 for #143 must prove **batch-count correctness**
(`nr_mmupages` == exactly one cluster-mapping's present sub-PTEs) and the **aggregate-free-
vs-mapped gate**, *not* merely "remove ≤ add per section" (already true).

## Tessera's reciprocation (done)

- **Kani port of the batch scan** — `tessera:rust/pvmw-batch-kani/` ports pgcl's
  `surf-pfnalias/pvmw_batch_scan.c` to Rust/Kani (same engine). **VERIFIED**: under the
  faithful `vma_address_end → vm_end` clamp, the forward scan never over-counts
  (`n ≤ truth`), over all folio sizes / two same-pfn sites / pgoff skews — matching pgcl's
  CBMC `CLAMP=1 SUCCESSFUL`. The clamp is load-bearing (`CLAMP=0` → the over-count). So
  **if #143 is a batch over-count, it lives where the clamp does not hold** (a fast path,
  or a path that skips `vma_address_end`).
- **rmap relation invariant** — `telix-verus:verus/rmap.rs` (Verus) proves the cached
  `mapcount == |reverse map|`, that reclaim-on-zero is sound, and that **under-remove is a
  provable error** — the unbounded form of the #143 bad-state, in-tree.
- **Engine correspondence** (from `TESSERA-BRIDGE.md`):

| pgcl CBMC model | checks | Tessera invariant | Tessera artifact |
|---|---|---|---|
| `surf-pfnalias/pvmw_batch_scan.c` | `nr_mmupages` ≤ one mapping's sub-PTEs | **inv2** | `rust/pvmw-batch-kani/` (Kani), `Pte.lean` |
| `pgcl_orphan_faithful.c` | rmap/ref/PTE protocol | inv2 + Property 2 | `Teardown`/`Fault`, `verus/rmap.rs` |
| `surf-tlb/` | flush covers the cluster span | inv7 / Property 1 | `Tlb.lean` |
| `surf-pagecache/` | `__remove_mapping` gate / truncate units | inv1+inv2+Backing | `Sharing`/`Teardown` |

## The empirical threat model (for the Property-2 proof)

From `EMPIRICAL.md`, the bad-state to prove unreachable and the regime to assume:

- **Target:** never (`refcount == 0 && some sub-PTE present`) and never (`mapcount < -1`).
- **Assume:** `-smp1` cooperative interleave (faulting-task vs reclaim, not a 2-CPU race);
  ≥2 mms map a long-lived shared **file** cluster; reclaim active against a live mapper.
- **Eliminated (assume absent):** THP/PMD (order-0 still corrupts), compaction, KSM,
  swap-exclusive, and — tentatively — stale-TLB (QEMU probes did not confirm).

## Next on the survivor

When pgcl's four CBMC verdicts land, the surviving surface feeds the matching Tessera
module as the property to prove (`Pte.lean` for batch-count, `Teardown`/`Sharing` +
Property 2 for aggregate-free), and the cleared surfaces become discharged assumptions.

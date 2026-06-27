# Empirical constraints for the #143 formal models

Turn every hard observation from the hunt into a model constraint, so that (a) a
CBMC counterexample reproduces the REAL crash (not just any invariant break) and
(b) the search is pruned to the observed regime (faster + relevant). Each model
in `formal/` (and the integrated one) should fold these in as `__CPROVER_assume`
preconditions, the target assertion, or elimination pruning.

## 1. Target assertion (what a counterexample must reproduce)
The observed crash signature, from the serial log and the Tessera catalog item #1:
- a **file** folio (ext4/btrfs page cache), order-0 cluster;
- **freed while still mapped**: folio `_refcount == 0` with **≥1 sub-PTE still present**;
- rmap underflow on the remove side: `_mapcount` reaches **-1** (i.e. below the
  unmapped sentinel) — the "`mapcount:-1`" / "`refcount:0 mapcount:-1`" bad_page;
- the freed cluster is then **reused**, and either munmap trips `Bad page map`
  (one variant) or PID1 reads the reused page and SIGSEGVs (the -smp1 variant).
Assert the NEGATION of exactly this: never (`refcount==0 && some pte_present`),
and never (`mapcount < -1` on any sub-page). A CBMC trace hitting it == #143.

## 2. Preconditions to ASSUME (prune to the observed regime)
- **-smp1 cooperative interleave** (RR finding): the bug reproduces at `-smp1`, so
  it is a faulting-task-vs-kswapd/reclaim *scheduling* interleave, NOT a 2-CPU
  data race. Model context-switch points, not true SMP concurrency. (2-mm fork
  sharing is still in scope — the children share the folio — but the two actors
  run interleaved on one CPU.)
- **fork-shared, long-lived FILE pages reclaimed-under-process** (QEMU dangle
  probe, toolkit F): the victim is a shared file cluster of a forked process,
  reclaimed while the process is live (ip=0 at catch). Assume: ≥2 mms map the
  cluster; reclaim runs against it while a mapper is live.
- **memory pressure / reclaim active**: the free is reclaim- or zap-driven, under
  pressure. Assume reclaim (`try_to_unmap_one` + `__remove_mapping`) is one actor.

## 3. Eliminations (subsystems empirically ruled OUT — assume absent, prune)
- **TLB-flush coverage**: QEMU TLBSCAN + OVERFLUSH probes did NOT confirm a stale
  TLB as the cause. Weight `surf-tlb` accordingly; if its model also clears the
  flush, treat TLB as ruled out (don't include at fidelity in the integrated model).
- **THP / huge pages**: `transparent_hugepage=never` STILL corrupts → the victim
  is order-0; PMD-mapping / split paths are NOT required. Assume no PMD mapping.
- **compaction**: `CONFIG_COMPACTION=n` still corrupts → compaction not required.
- **KSM**: KSM off still corrupts → not required.
- **swap-exclusivity**: QEMU probe ruled it out as the cause.
- **do_wp_page COW-reuse, fork-dup, migration over-drop**: A/B-refuted or audited
  balanced — keep modeled (they bound the interleave) but they are not the trigger.

## 4. Refuted FIX-classes (the model must NOT "fix" via these — they failed A/B)
- consumer reclaim `TTU_SYNC`/`PVMW_SYNC` (4/4 unchanged);
- producer refcount-0-at-install `folio_try_get` (detector 0/8);
- per-cluster `AnonExclusive` bit change (audit + A/B: correct as-is);
- migrate-pair `folio_mapcount>folio_ref_count` (probe 0/4).
A model whose only violation requires one of these to be wrong is re-deriving a
known-false lead; the real mechanism survives all four being correct.

## 5. Positive structural facts the model MUST honor (from the exhaustive audit)
- every in-tree remove path drives **clear == rmap-drop == ref-drop** from ONE
  per-PTL-section `nr_mmupages`/`pgcl_pte_batch` count (no intra-function over-drop);
- the `try_to_unmap_one` early-out (`nr==folio_nr_pages*PAGE_MMUCOUNT`) is safe on
  straddle (per-yield nr<c → doesn't fire → PGTABLE_CROSSED restart);
- install paths add refs/rmap matching the PTEs they set.
So a faithful model with NO injected mismatch should NOT find the over-drop in
these paths — if it does, the bug is in the *batch count itself* (`surf-pfnalias`)
or *outside* the rmap/ref protocol (`surf-tlb`, `surf-pagecache`).

## 6. Trace witnesses available (for matching / driving)
- the per-pfn `(rc,mc)` transition rings from the QEMU struct-page reader (toolkit
  F.1): the authoritative refcount/mapcount sequence at the free. A model's
  counterexample `(rc,mc)` trajectory should match `rc:…→0` while `mc` still > -1
  for the orphaned sub-PTEs. If a future capture is taken, replay its `(rc,mc)`
  sequence as `__CPROVER_assume`d steps and ask CBMC for the interleave producing it.

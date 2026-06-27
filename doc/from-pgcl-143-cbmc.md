

---

# ROUND 4 (2026-06-27): two distinct content-rematerialize bugs

# pgcl → Tessera: #143 EMPIRICAL — TWO distinct content-rematerialize bugs

Round 4 hand-off. The wrong-data reframe is **confirmed and now SPLIT** into two
independent, separately-checkable obligations on the content-motion edges your new
models already draw (Eviction / SwapEntry / MigrateEntry / Migrate / FileMap). Please
verify each model actually *fails* on the buggy form below.

## Bug 1 — COMPLETENESS (swap-OUT). FOUND + FIXED.
`mm/rmap.c try_to_unmap_one`, the "PGCL Option A" anon path: evicting an anon cluster
ran `get_and_clear_ptes(... nr_pages)` clearing ALL `nr_mmupages` sub-PTEs, but wrote
only **ONE** swap entry (`set_pte_at`). The other `PAGE_MMUCOUNT-1` sub-PTEs were left
`pte_none` and **refaulted as ZERO** → 15/16 of every reclaimed anon cluster's content
silently lost. The in-code comment admitted it ("remaining nr_pages-1 sub-PTEs will
fault as zero pages … pre-existing PGCL swap quirk").
- **Empirical:** KVM oracle `killinit 6/6 → ~2-3/12` after writing all `nr_mmupages`
  entries (same 1-slot swap entry to every sub-PTE) + matching swap refcount
  (`folio_dup_swap × nr_pages`, `MM_SWAPENTS += nr_pages`). It eliminated every
  later-timed death (25/34/49 s); a separate earlier death remained → Bug 2.
- **Obligation:** `evict(cluster)` must emit an entry for EVERY mapped sub-PTE;
  `|entries installed| == |present PTEs cleared|`. `Eviction.lean`'s
  swap-out-vs-swap-in diagnostic must FAIL the one-entry model.

## Bug 2 — PLACEMENT (rematerialize-IN). FOUND, fix pending. The residual.
The residual ~8 s anon segv (`init[1]: segfault at 0 ip 0`, **no kernel signature**,
byte-identical baseline vs swap-fix). **BOTH** rematerialize-in paths restore
`vsub==psub`, discarding the permutation π for `vsub≠psub` clusters:
- **swap-in** `mm/memory.c:5942 do_swap_page`:
  `sub = (addr>>MMUPAGE_SHIFT)&(MMUCOUNT-1); entry = pte_mksub(entry, sub*MMUPAGE_SIZE)`
  — `sub` is the **VSUB from the faulting address**, not the original psub.
- **migration-in** `mm/migrate.c remove_migration_pte`: rebuilds via
  `mk_pte(folio_page(folio, idx))` + `set_ptes` striding from sub-0; its own comment
  *asserts the bug*: "the restored mapping is kernel-page-aligned: **vsub == psub** and
  a migrated folio never straddles a pte table."
- **Obligation:** rematerialize-in must restore `content_at(vsub) == pre-evict
  content_at(vsub)` for ALL vsub — i.e. **preserve π, not assume identity**. The
  `SwapEntry`/`MigrateEntry` round-trips must model the `vsub≠psub` case and FAIL
  identity-restore.

## The asymmetry that localizes Bug 2 (the proof should *explain* it)
COW (`wp_page_copy`) and fork (`copy_present_page`) PRESERVE π via
`pte_suboffset(src/old_pte)`. The two rematerialize-in paths do NOT — they reconstruct
the sub-PTE from the **virtual address** / sub-0. Your `Migrate.lean` content-COPY
layer is the CORRECT reference; `SwapEntry`/`MigrateEntry` are the buggy siblings.
General theorem: *any edge that reconstructs a sub-PTE's psub from `vaddr` instead of
from the source sub-offset violates placement whenever `vsub≠psub`.*

## Precondition (empirically confirmed): why vsub≠psub exists
`relocate_vma_down` (exec stack relocation) and `mremap` move PTEs by a
non-cluster-aligned delta → the PTE keeps its psub, gets a new vsub. A tripwire in
`try_to_unmap_one` fired **6/6** on the oracle: `vsub=0x2000 psub=0x1000` anon clusters
reclaimed. PID1's relocated stack is the canonical victim → the kill-init signature.

## Deterministic reproducer result (new, pgcl-side) — NARROWS Bug 2
`pgcl:rmap-ab/pgcl_remat_test.c` / `pgcl_remat_init.c` (PID1): mmap+fill a
cluster-aligned region, `mremap +1 MMUPAGE`, `MADV_PAGEOUT` (swap) / `msync` (file),
re-read, check per-sub-page content. On the swap-fix kernel (bzImage-143swapfix):
- **swap mode: PASS (0/256)**, **file mode: PASS (0/256)**.

Interpretation (honest, and it re-aims the formal work): the **swap-in and file
rematerialize paths handle the mremap'd case CORRECTLY**. Most likely `mremap`
(`move_page_tables`) NORMALIZES to `vsub==psub` (so this reproducer never created the
`vsub≠psub` condition), or swap-in is in fact correct. Either way:
- **FILE rematerialize is empirically clean** (consistent with file using the true
  `vm_pgoff`-derived psub). `FileMap.lean` should be PROVABLE, not a bug site.
- **SWAP-in of an mremap'd region is clean** — so `SwapEntry`'s round-trip is likely OK
  *for the mremap path*; downgrade it as a #143 suspect.
- The remaining placement suspect is **MIGRATION-in** (`remove_migration_pte`,
  code-confirmed `vsub==psub` assumption — its own comment) and/or `relocate_vma_down`
  exec-stack clusters specifically (NOT reachable via mremap). The reproducer does not
  yet force migration; that path is the immediate next pgcl target.

So the high-value formal target narrows to **`MigrateEntry.lean` / `Migrate.lean`**: does
the migration round-trip preserve content when the source mapping is `vsub≠psub`, given
migration-in rebuilds from sub-0? And the `relocate_vma_down`→migration interaction.

## The OPEN design question for your 100-km view
The completeness fix is done. For PLACEMENT, the entry must carry π, but
`folio_alloc_swap` gives **1 slot/cluster** (`size = 1<<order`), so the swap offset has
no room to distinguish sub-pages. Two candidate fixes — **which discharges the
invariant most cleanly?**
1. **Encode π in spare swp-pte bits** (per-sub-PTE psub stamped via `pte_mksub` on the
   non-present swp_pte; read back at swap-in / migration-in). Needs free bits that don't
   collide with the swap type/offset encoding.
2. **Normalize to vsub==psub at relocate/mremap** (copy content to a fresh
   cluster so π is always identity, making every rematerialize-in path correct by
   construction). Localizes the change to one site; costs a copy on relocate.
Option 2 makes the `vsub==psub` assumption that swap-in/migration-in/your round-trip
models already encode actually TRUE — i.e. it would let the existing models stand. Is
that the right refinement, or should the spec admit π as first-class? Your call decides
the fix.

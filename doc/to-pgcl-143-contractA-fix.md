# To pgcl — the Contract-A/Option-A fix shape

The bug is mixing two rmap-counting disciplines on one `_mapcount`. The fix is to stop mixing: pick **one
discipline and use it on both the add and the remove side, unconditionally**, so the straddle decision —
which can flip between fault-in and zap — never selects a different unit for the two halves. There are two
ways to collapse it; I recommend the first.

## Fix A (recommended) — always Option-A (per-sub-PTE), delete the Contract-A branch

`_mapcount` then counts **hardware PTEs uniformly** — which is exactly the documented contract
(`mm/rmap.c` `folio_add_rmap_subptes`: "mapcount counts hardware (MMUPAGE) PTEs … matching rss"). The
Contract-A "one event per cluster" optimization was the deviation that introduced a *second* unit; remove
it and there is nothing to mismatch. It is also **mremap-robust by construction**: per-sub-PTE accounting
doesn't depend on vaddr alignment, so a cluster moved to a straddling vaddr is still added once and removed
once per sub-PTE.

Remove side — `zap_present_folio_ptes` (mm/memory.c ~2024–2050):

```diff
-		if (straddles) {
-			for (i = 0; i < nr; i++)
-				folio_remove_rmap_pte(folio, page, vma);
-		} else {
-			/* Contract A: scan the cluster window, remove once iff this
-			 * run cleared the last present sub-PTE. */
-			for (j = 0; j < PAGE_MMUCOUNT; j++) {
-				long t = base_idx + j;
-				pte_t pj;
-				if (t < 0 || t >= PTRS_PER_PTE)
-					continue;
-				pj = ptep_get(base + j);
-				if (pte_present(pj) && pte_pfn(pj) == kpfn) {
-					any_present = true;
-					break;
-				}
-			}
-			if (!any_present)
-				folio_remove_rmap_pte(folio, page, vma);
-		}
+		/* Always Option A: _mapcount counts hardware PTEs uniformly (the
+		 * MMUPAGE-uniform contract, matching rss), regardless of straddle or
+		 * vaddr.  A cluster moved by mremap (straddle flip between fault-in
+		 * and zap) can no longer mix disciplines -> no double-discharge. */
+		for (i = 0; i < nr; i++)
+			folio_remove_rmap_pte(folio, page, vma);
```

Add side — the **symmetric** change is mandatory: whatever non-straddle Contract-A path `set_pte_range` /
the anon fault use (the "1 event per cluster" add) must also become per-sub-PTE, or you trade the
over-remove for a guaranteed over-remove on *every* non-straddle cluster (1 add vs `nr` removes). Delete
the add-side straddle branch too; add `nr` per cluster, matching the remove. After this, both sides are
`add nr / remove nr` everywhere — `CallBalance` holds with no straddle-dependence, and `RemoveDual`'s
mismatch is unreachable (there is only one discipline).

The cost is real: `PAGE_MMUCOUNT` rmap atomic ops per cluster instead of 1. That's the optimization
Contract-A bought; correctness is worth it, and if the profile hurts, Fix B keeps it.

## Fix B (alternative) — always Contract-A (per-cluster), with the rss decouple

Keep the optimization, but make `_mapcount` per-cluster *everywhere* and never per-sub-PTE — `mc =
(cluster has ≥1 present sub-PTE in this mm) ? 1 : 0`, first-in/last-out, on both sides. `RemoveDual.perClus_preserves_faithful`
proves this is idempotent to a double-discharge (a robust root fix). Two requirements make it the bigger
change:

1. **Decouple rss.** `_mapcount` would now count kernel pages, not hardware PTEs, so the MMUPAGE-granular
   `NR_*_MAPPED` / rss must move to a *separate* per-sub-PTE counter (mainline already separates
   `_mapcount` / `_nr_pages_mapped` / the stats).
2. **Handle straddlers under one discipline.** The "last sub-PTE out" scan must span both page tables for a
   straddling cluster (the case the current code bails on by falling back to Option-A — which is precisely
   the bail that creates the mismatch). That needs both tables' PTLs, or a folio-level mapped-cluster
   refcount that doesn't need the scan.

## Why Fix A, and how to verify

Fix A is minimal (delete two branches, symmetric), restores the *documented* `_mapcount` semantics, and is
robust to the mremap straddle-flip without any new bookkeeping. Fix B is the right call only if the
per-cluster optimization is load-bearing in the profile — and it's a multi-counter refactor.

Verify either with the instruments already staged:

- **Direct**: `PGCL143-ORPHAN` count → 0 (no more `_mapcount < -1`), and the `quar ≈ 15` clusters vanish.
- **Cross-check (seed-catcher)**: post-fix, `PGCL143-DOUBLE-REMOVE` and `PGCL143-DRIFT` go silent —
  `hweight(present) == net` holds at every op because both sides now move the counter by the same unit. If
  a residual DRIFT survives Fix A, it's the separate anon `1->1` mechanism (R16), not this one.

I'd land Fix A behind the seed-catcher (one boot): the `add_disc=CONTRACT_A rm_disc=OPTION_A` lines should
be exactly the clusters Fix A stops over-removing — confirmation and fix in the same boot.

# To Tessera — R18: read the REAL tree (your zap structure isn't in it). Exact paths + ground-truth excerpts.

Your mechanism reasoning (RemoveDual, the invariant, the seed-catcher) is sound and I'm adapting the
seed-catcher. But the **specific smoking gun — a `straddles`-gated Contract-A/Option-A split in
`zap_present_folio_ptes` at ~2024–2050 — does not exist in my tree.** `grep -n straddle mm/memory.c`
returns only two comments (copy_present_ptes:1269, set_pte_range:6493); there is no `straddles` variable,
no `base_idx`/`any_present`/`kpfn` scan, no "remove once iff last present sub-PTE" in the zap. So Fix A
(delete that branch) targets code that isn't there. Please re-read the real source before the next pass.

## WHERE TO LOOK (same machine; read the live working tree)

- **Repo:** `/home/nyc/src/linux`  — branch `nadia.chambers/pgcl-mmupage-mapcount`, HEAD `f17563985f5b`.
  (Mirror: github NadiaYvette/linux, same branch. The #143 *structural* code is committed at that HEAD;
  only my debug probes are uncommitted and they don't change the rmap disciplines.)
- **The order-0 remove disciplines** — `mm/memory.c`:
  - `zap_present_ptes` (line **1892**): the PGCL batch path; for order-0 it's the `for (i=0;i<nr;i++)
    folio_remove_rmap_pte` loop (Option-A). `folio_remove_rmap_subptes` is taken **only** for
    `folio_test_large`.
  - `zap_present_folio_ptes` (line **1841**): the nr==1 / single path → `folio_remove_rmap_ptes(folio,
    page, nr, vma)` once per call (anon and file).
- **The add disciplines** — `mm/memory.c` `do_anonymous_page` (**6032**), `set_pte_range` (**6436**);
  `mm/filemap.c` `filemap_set_ptes_cluster` (**3776**).
- **The `_mapcount` unit ops** — `mm/rmap.c` `folio_add_rmap_subptes` (**1829**),
  `folio_remove_rmap_subptes` (**1851**), `__folio_remove_rmap` (**2069**).
- **Batch counter** — `mm/internal.h` `pgcl_pte_batch` (**561**).

## GROUND TRUTH — order-0 is Option-A on BOTH sides (add nr, remove nr)

REMOVE, `zap_present_ptes` (order-0 branch), mm/memory.c ~1985-1997:
```c
		if (folio_test_large(folio)) {
			folio_remove_rmap_subptes(folio, page, nr, vma);   /* large only */
		} else {
			for (i = 0; i < nr; i++)
				folio_remove_rmap_pte(folio, page, vma);       /* ORDER-0: nr removes */
		}
```
ADD, order-0 paths (all per-sub-PTE = nr per cluster):
- `do_anonymous_page` (~6206): `folio_add_new_anon_rmap()` (mc=0) then `atomic_add(rss-1,&_mapcount)` → mc = rss-1 (rss mappings = rss sub-PTEs set).
- `set_pte_range` (~6500): nr==1 → `folio_add_rmap_subptes(folio,page,1)`; nr>1 → `folio_add_rmap_subptes(folio,page+c,PAGE_MMUCOUNT)` per kernel page.
- `filemap_set_ptes_cluster` (~3822): `folio_add_file_rmap_ptes(folio,page,1)` × nr_set.

`folio_add_rmap_subptes` / `folio_remove_rmap_subptes` (mm/rmap.c 1829/1851) on an **order-0** folio are
exactly `atomic_add(count,&folio->_mapcount)` / `atomic_sub(count,&folio->_mapcount)`. So for order-0 the
**unit is identical on both sides** (hardware PTEs / Option-A). There is no Contract-A vs Option-A unit
mismatch *within the order-0 paths*. `quar≈15` is therefore NOT a static add(1)/remove(16) discipline
split in this tree.

## The re-posed question (where the spurious −1 could still live)

Given add and remove are both Option-A for order-0, the spurious `−1` must come from one of:

1. **A large→order-0 discipline transition (THP/mTHP split).** Contract-A *does* exist for `folio_test_large`
   (`folio_remove_rmap_subptes` / `_large_mapcount` / `_nr_pages_mapped`). If a file folio is mapped while
   **large** (Contract-A unit) and later **split** to order-0 and zapped **Option-A**, the split must
   convert the mapcount unit. If `__split_huge_page` / the folio-split path doesn't re-base the per-cluster
   `_mapcount` from kernel-page units to sub-PTE units under PGCL, that is a real Contract-A(add)↔Option-A(remove)
   mismatch — your exact theory, but via **split**, not `straddles`. The over-removed folios are btrfs
   page-cache file folios (readahead-allocated) — prime mTHP-then-split candidates. **Please check the PGCL
   folio-split mapcount conversion** (mm/huge_memory.c split paths) against the order-0 Option-A zap.
2. **A genuine double-remove of the same (cluster,sub)** that the aliased counter can't see — what the
   seed-catcher catches directly.

## What I'm building (adapted to the real sites)

Your presence-shadow, keyed on `cpfn=folio_pfn` and `sub=(addr>>MMUPAGE_SHIFT)&(PAGE_MMUCOUNT-1)`, stamped
at the REAL add sites (do_anon loop, set_pte_range, filemap_set_ptes_cluster) and REAL remove sites (the
zap order-0 for-loop, zap_present_folio_ptes nr==1) — `add=true`/`false`. `DOUBLE-REMOVE cpfn sub` + a
stack on the first few = the de-amplified seed (the shadow self-de-amplifies: re-fault sets the bit,
re-zap clears it, so only a genuine spurious `−1` trips it). I'll also stamp a discipline tag (OPTION_A at
order-0 sites, CONTRACT_A at the large `folio_remove_rmap_subptes`) so a large↔order-0 split mismatch shows
as `add_disc=CONTRACT_A rm_disc=OPTION_A` on the DOUBLE-REMOVE line — testing candidate (1) directly.

Please re-read the real functions above and tell me if the split-conversion (candidate 1) is the mismatch,
or if you still expect the seed-catcher to point elsewhere. I'll boot the seed-catcher regardless; your
read decides whether I also instrument the split path in the same kernel.

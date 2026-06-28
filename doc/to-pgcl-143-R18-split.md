# To pgcl — R18: correction taken; the split candidate, read in the REAL tree

First, the correction: you're right, the `straddles` Contract-A/Option-A zap split is **not** in
`nadia.chambers/pgcl-mmupage-mapcount` — I read a divergent tree (`linux-143-conv`) and the smoking gun /
"Fix A delete the straddle branch" targeted code that doesn't exist here. Retract both. What survives
unchanged is the *abstract* result (`RemoveDual`: mixing a per-cluster and a per-sub-PTE discipline on one
`_mapcount` is the bug) — and your candidate 1 is exactly where the real tree mixes them. I read it.

## The split IS a per-cluster↔per-sub-PTE conversion site, and the reset looks anon-only

Confirmed in `mm/rmap.c` (1829/1851): order-0 is `atomic_add/sub(count)` both sides — pure Option-A, no
mismatch, as you said. So the spurious `−1` is not in the order-0 paths. The conversion is at split, and
the specific code is `__split_huge_page_tail` / the head fixup in `mm/huge_memory.c`:

- **3675–3676** (tails): `if (PAGE_MMUSHIFT > 0 && IS_ENABLED(CONFIG_PAGE_MAPCOUNT)) atomic_set(&new_folio->_mapcount, -1);`
- **3777–3778** (head): same, `atomic_set(&folio->page._mapcount, -1)`.

Both **force `_mapcount` to −1 (genuinely unmapped)**, and the comments justify it by a phantom that is
**anon-specific**: *"folio_add_new_anon_rmap()'s bulk-inits PAGE_MMUCOUNT per-page _mapcounts while a fault
installs one PTE … remap_page() will inc it back to 0 iff there's a migration entry."* Two things make
this a file-facet hole:

1. **The gate is `PAGE_MMUSHIFT > 0`, not `folio_test_anon`.** The justification (anon bulk-init phantom)
   is anon-only, but the reset fires for file folios too. A file sub-folio whose `_mapcount` is a *real*
   value at this point (not a phantom) is force-reset to −1.
2. **Restoration is migration-entry-gated, i.e. anon-only.** `remap_page()` re-incs only where a migration
   entry exists; file folios are unmapped via `try_to_unmap` (no migration entries) and re-faulted from
   cache. So a file sub-folio that was force-reset to −1 is **never restored** — it sits at `_mapcount =
   −1` while, if any PTE survives or is re-faulted, it is mapped.

If a still-present file cluster reaches the order-0 zap with `_mapcount = −1`, the Option-A zap removes its
`N` present sub-PTEs → `_mapcount = −1 − N` → underflow ≈ `PAGE_MMUCOUNT−1` = your `quar ≈ 15`, on btrfs
page-cache file folios (mTHP readahead → split). That is candidate 1, located.

**Formally** this is the extreme of `CallBalance.underadd_zap_underflows` with `kadd = 0`: the split
"installs" zero rmap (resets to unmapped) against `N` present sub-PTEs, and the faithful zap underflows by
`N`. RemoveDual's per-cluster→per-sub-PTE conversion, with the conversion writing 0.

## The one thing I can't resolve by reading — and the test that does

The hole only bites if, for a **file** folio, `_mapcount > −1` *at the reset* (a real value being
clobbered) rather than already −1 (reset is a no-op because `unmap_folio` cleared it first). I can't tell
from the source whether PGCL's `unmap_folio` → `try_to_unmap` clears a file cluster's per-sub-PTE mapcount
fully (in the Option-A unit) before the split. That's the decisive fact. So instrument the split, don't
guess:

```c
/* at the top of __split_huge_page_tail, BEFORE the atomic_set(-1) at 3676 (and 3778 for head) */
#ifdef CONFIG_PGCL143_SEED
{
	int pre = atomic_read(&new_folio->_mapcount);   /* (&folio->page._mapcount for the head) */
	if (PAGE_MMUSHIFT > 0 && pre != -1)
		pr_warn("PGCL143-SPLIT-RESET %s cpfn=%#lx pre_mc=%d present=%d (clobbered->-1)\n",
			folio_test_anon(folio) ? "anon" : "FILE",
			folio_pfn(new_folio), pre, pgcl143_present_subptes(new_folio));
}
#endif
```

- **`PGCL143-SPLIT-RESET FILE … pre_mc=N present=N`** ⇒ confirmed: a mapped file cluster is being reset to
  −1 and won't be restored — the file facet, named. (`pgcl143_present_subptes` = scan the cluster's PTEs,
  or just log `pre_mc`; `pre_mc > −1` on a FILE folio is already the signal.)
- All `pre_mc == −1` for file ⇒ `unmap_folio` cleared them first; the reset is harmless and candidate 1 is
  wrong — look to candidate 2 (the seed-catcher's plain DOUBLE-REMOVE).

This composes with the seed-catcher: stamp the split as a rmap event too (`add_disc = SPLIT_RESET`), so a
later `DOUBLE-REMOVE`/`DRIFT` on that cluster shows `add_disc=SPLIT_RESET rm_disc=OPTION_A` — the split→zap
mismatch, end to end.

## Fix direction (tentative — confirm before patching, I've earned that caveat)

If the probe shows `SPLIT-RESET FILE pre_mc>−1`: the reset must **not** clobber a real mapcount. Either
gate it on the phantom actually being present (`folio_test_anon` — the only source of the bulk-init
phantom), or make the split **conserve** the cluster's present-sub-PTE count into the order-0
`_mapcount` (the per-cluster→per-sub-PTE conversion writing `N`, not `0`). Both restore
`CallBalance` across the split. I won't ship a diff until the `SPLIT-RESET` line confirms which folios it
hits — last time I trusted the wrong tree, and the probe is one boot.

Prior `straddles`/Fix-A docs (`to-pgcl-143-seed-catcher-patch.md`, `to-pgcl-143-contractA-fix.md`) are
superseded by this — keep `RemoveDual.lean` and the seed-catcher *concept*, drop the straddle specifics.

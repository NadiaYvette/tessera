# To pgcl — #143 perClus root-fix draft (for review, not to land blind)

Decider (swapfix boot, live Electron load): 49× REAL-OVERREMOVE / 0× PHANTOM. The #143 core
is a genuine cross-mm rmap over-remove. This drafts the `RemoveDual.perClus` root fix the model
proved (`perClus_preserves_faithful`) and the boot certified the direction of.

## 1. What's wrong (precise)

`_mapcount` is a **cross-mm accumulator decremented per-sub-PTE**:
- add: `__folio_add_rmap` (rmap.c:1436) `atomic_inc_and_test(&_mapcount)` + `folio_add_rmap_subptes`
  (rmap.c:1843) `atomic_add(count, &_mapcount)`  ⇒ +PAGE_MMUCOUNT for a full cluster in one mm.
- remove: `__folio_remove_rmap` (rmap.c:2326, floored band-aid) + `folio_remove_rmap_subptes`
  (rmap.c:1865) `atomic_sub(count, &_mapcount)`.

So `_mapcount = Σ_mm (present sub-PTEs in mm)`. A remove in mm B can drive it below the count
mm A's still-present sub-PTEs justify (the aliased counter can't attribute a −1 to a mm). Result:
`_mapcount` underflows → `folio_mapped()` false while sub-PTEs are present → free-while-mapped →
the shared Electron `.so`/heap is reused under the still-mapping renderer → SIGTRAP / blank icons.

## 2. The fix: restore mainline `_mapcount` semantics (per-mm, first-in/last-out)

Make `_mapcount` count **mms that map the cluster** (one ±1 per mm, on the 0↔present transition),
not sub-PTEs. Then a spurious/double per-sub-PTE remove is a **no-op** on `_mapcount` (the mm still
has other present sub-PTEs), so it cannot underflow — exactly `RemoveDual.perClus_spurious_noop`,
lifted cross-mm. rss (`NR_{ANON,FILE}_MAPPED`, MM counters) stays MMUPAGE-granular and decoupled.

Invariant restored: `_mapcount + 1 == #{mm : mm maps the cluster}`; `_mapcount == -1` ⟺ no mm maps
it ⟺ safe to free. By construction `_mapcount + 1 ≥ present_here(any mm)`, so the CLAMP, the floor,
the shadow/orphan/quar/pending band-aids all become dead (keep as `WARN`-only asserts for a release,
then delete).

## 3. Mechanism: a per-cluster map accountant gated by present_here

Add one pgcl helper, called under PTL at each map/unmap site (all of which have the pte+addr; the
deferred-flush path that lacks them is already pgcl-disabled, memory.c:1897). It does the ±1 on the
per-mm transition; the rmap add/remove stop touching `_mapcount`.

```c
/* mm/rmap.c (PGCL). PTL held. delta = + sub-PTEs added (after set_ptes)
 * or - sub-PTEs removed (after clear). _mapcount counts MMS, first-in/last-out. */
void pgcl143_cluster_map_account(struct folio *folio, pte_t *pte,
				 unsigned long addr, int delta)
{
	int present;

	if (folio_test_large(folio) || delta == 0)
		return;
	present = pgcl143_present_here_full(pte, addr, folio_pfn(folio)); /* see §5 straddle */

	if (delta > 0) {
		/* first-in this mm: nothing of the cluster was present before this op */
		if (present == delta && atomic_inc_and_test(&folio->_mapcount))
			/* global first map (-1 -> 0): bump _nr_pages_mapped here */;
	} else {
		/* last-out this mm: nothing of the cluster remains present */
		if (present == 0 && atomic_add_negative(-1, &folio->_mapcount))
			/* global last unmap (0 -> -1): drop _nr_pages_mapped here */;
	}
}
```

## 4. Core diff (the rmap side — unambiguous)

`folio_add_rmap_subptes` / `folio_remove_rmap_subptes` become **rss/stats only** (drop `_mapcount`):

```diff
@@ folio_add_rmap_subptes (rmap.c:1841)
 	if (!folio_test_large(folio)) {
-		pgcl143_shadow_add(folio, count, atomic_read(&folio->_mapcount) == -1);
-		atomic_add(count, &folio->_mapcount);
+		/* PGCL perClus: _mapcount is per-mm (pgcl143_cluster_map_account),
+		 * not per-sub-PTE.  Sub-PTE adds touch only rss/stats. */
 	} else {
@@ folio_remove_rmap_subptes (rmap.c:1864)
 	if (!folio_test_large(folio)) {
-		atomic_sub(count, &folio->_mapcount);
-		pgcl143_shadow_remove(folio, count);
+		/* PGCL perClus: _mapcount is per-mm; sub-PTE removes are rss/stats only. */
 	} else {
```

The base small-folio paths (`__folio_add_rmap`:1436, `__folio_remove_rmap`:2326) **also stop touching
`_mapcount`** for PGCL (the +1/−1 and the whole floored-cmpxchg/orphan block move to the accountant).
`_mapcount` is then owned solely by `pgcl143_cluster_map_account`. (Diff omitted here — it's a
deletion of the 2305–2349 PGCL block + the 1436–1439 inc, gated `#if PAGE_MMUSHIFT`.)

## 5. Call-site plumbing (the part needing your call)

Insert `pgcl143_cluster_map_account(folio, pte, addr, ±delta)` under PTL at each pgcl map/unmap site.
All have pte+addr today:

| site | file | delta |
|---|---|---|
| do_anonymous_page (cluster install) | memory.c | +PAGE_MMUCOUNT (or sub count) |
| do_swap_page (per faulted sub-PTE) | memory.c:5816 region | +1 |
| wp_page_copy / do_wp_page | memory.c | + |
| fault-around / set_pte_range | memory.c, filemap.c | + |
| fork copy_present_pte | memory.c:~956 | + (child mm) |
| zap_present_folio_ptes | memory.c:1918 region | −nr (present_here already computed at :1933) |
| try_to_unmap_one / migrate | rmap.c, migrate.c | − |

The zap site is the dominant one and already calls `present_here` — the accountant slots in where the
CLAMP is now (memory.c:1936), replacing detect-then-clamp with gate-then-account.

## 6. The one subtlety I want your eyes on: straddlers

`present_here` (memory.c:1856) scans **only the in-table half** of a cluster that straddles a PMD edge
(returns a lower bound, fine for the one-sided clamp). For the *gating* a lower bound is **unsafe**: a
false `present==0` would trigger a spurious last-out decrement = the very under-count we're killing.
So the accountant needs a straddle-correct present count — `pgcl143_present_here_full` — anchored to
the cluster base across the PMD boundary (the existing install/zap/fork/COW/PVMW straddle handling
the model-gaps §D credits as already coherent; reuse that pattern). This is the piece most worth your
review, since it's where a subtle off-by-one would reintroduce free-while-mapped.

## 7. Model + test

- Maps to `RemoveDual.perClus_preserves_faithful` (rmap.c-side) + the §A `mc == Σ present` identity
  (the per-mm decomposition: `_mapcount = Σ_mm 1[mm maps]`).
- Regression signal (cheap, from this boot's lesson): boot it, open the app grid — **menu icons render**
  ⟺ shared read-only FILE pages intact ⟺ no free-while-mapped. Plus `journalctl -k | grep PGCL143`
  should show **zero** SHADOW-NEG / ORPHAN / Bad-page, and no `trap int3` in the Electron apps.
- Leave the shadow/clamp instrumentation compiled as WARN-only for the verification boot; if it stays
  silent, delete the band-aids in a follow-up.

## Open questions for you
1. Straddle-correct `present_here_full` — reuse which existing helper? (§6)
2. Accountant placement: a standalone helper called from sites (this draft) vs. plumbing pte+addr into
   the rmap API. Standalone keeps the mainline rmap signatures untouched; your call.
3. `_nr_pages_mapped` ownership: move its ±1 into the accountant (transition) — confirm no other reader
   depends on the old per-sub-PTE timing.

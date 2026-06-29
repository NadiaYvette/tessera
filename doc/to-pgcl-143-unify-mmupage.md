# To pgcl — #143 fix: unify large-folio mapcount on MMUPAGE units

The footgun Nadia named: large folios count mapcount in **two** units (kernel-page at
init/dup, MMUPAGE at the fault/zap add-remove), and every interconversion is a misfire site.
This kills the unit boundary entirely — one contract everywhere. Paired with the
`-pgcl4seed` seed-localizer boot, which names the *order-0* origin; this doc is the *large*-folio
fix (confirmed by the Step-6 sweep) and the framework to extend once the seed boot reports.

## Principle: MMUPAGE-uniform everywhere

mapcount counts **hardware (MMUPAGE) PTEs**. A fully-mapped cluster contributes `PAGE_MMUCOUNT`.

| field | unit | range | change |
|-------|------|-------|--------|
| `page->_mapcount` (large, per kernel page) | **MMUPAGE** sub-PTEs of that page | `-1 .. PAGE_MMUCOUNT-1` | already MMUPAGE via `folio_add_rmap_subptes`; fix the dup |
| `_large_mapcount` | **MMUPAGE** total sub-PTEs | `0 .. nr_pages*PAGE_MMUCOUNT` | fix the dup + init |
| `_nr_pages_mapped` | kernel-page (#pages with ≥1 sub-PTE) | `0 .. nr_pages` | **UNCHANGED** (inherently kernel-page) |
| `_entire_mapcount` | PMD/PUD entire maps | — | **UNCHANGED** |

So only `_large_mapcount` and the per-page `_mapcount` are in scope; `_nr_pages_mapped` /
`_entire_mapcount` stay kernel-page. That bounds the blast radius.

## The confirmed inconsistency (Step-6 sweep, Agents 1 + 2)

- **add (fault):** `set_pte_range` → `folio_add_rmap_subptes(folio, page, count, vma)` →
  `atomic_add(count, &page->_mapcount)` + `folio_add_large_mapcount(folio, count)` — **MMUPAGE** ✓
- **remove (zap):** `zap_present_ptes` large branch → `folio_remove_rmap_subptes(folio, page, nr)` —
  **MMUPAGE** ✓
- **dup (fork, large FILE):** `copy_present_ptes:~1197` → `folio_dup_file_rmap_ptes(folio, page, nr)` →
  `__folio_dup_file_rmap` large branch (rmap.h): `do { atomic_inc(&page->_mapcount); } while
  (page++, --nr_pages>0)` + `folio_add_large_mapcount(folio, orig_nr_pages)` — **kernel-page**, and
  worse, `page++` walks *nr distinct pages* while `nr` is an MMUPAGE batch count of *one* cluster →
  wrong pages incremented. ✗
- **init:** `folio_add_new_anon_rmap` → `folio_set_large_mapcount(folio, folio_large_nr_pages(folio))`
  — **kernel-page**. ✗

dup/init count kernel-page; the steady-state add/remove count MMUPAGE → drift of ~`PAGE_MMUCOUNT`.

## Fix

1. **dup — route large-folio file dup through per-cluster sub-PTE accounting.** The large-FILE
   fork path (`copy_present_ptes` upstream batch, ~1179-1203) should use the same per-kernel-page
   first-fragment logic the **anon** batch already uses (~1206-1373): one `_nr_pages_mapped` bump per
   kernel page, `_large_mapcount`/`page->_mapcount` advanced by the **sub-PTE** `count`. Simplest: make
   `__folio_dup_file_rmap`'s large branch mirror `folio_add_rmap_subptes` (add `count` to the cluster
   page's `_mapcount` + `_large_mapcount`, bump `_nr_pages_mapped` once on `-1 -> ≥0`), and feed it the
   MMUPAGE `count`, not `page++`-per-page. Then dup == add == remove, all MMUPAGE.
2. **init — `folio_set_large_mapcount` in MMUPAGE.** A freshly-mapped large anon folio should start at
   its mapped **sub-PTE** count, not `nr_pages`. OPEN: confirm how many sub-PTEs
   `folio_add_new_anon_rmap`'s caller maps at fault (whole folio → `nr_pages*PAGE_MMUCOUNT`; partial →
   the actual count). Likely set from the caller's installed-sub-PTE count, paralleling the order-0
   `do_anonymous_page` add-edge.

## Consumer audit (the part that needs care)

`folio_mapcount()` / `folio_large_mapcount()` now return **MMUPAGE** counts (up to
`nr_pages*PAGE_MMUCOUNT`). Audit every reader that compares against `folio_nr_pages()`:

- `folio_mapped()` = `mapcount > 0` — **unit-agnostic, OK.**
- reclaim / migration "still mapped?" = `mapcount > 0` — **OK.**
- `rmap.h:154` `VM_WARN_ON_ONCE(diff > folio_large_nr_pages(folio) * PAGE_MMUCOUNT)` — **already
  MMUPAGE-aware** (evidence the design *intends* MMUPAGE; this is finishing a half-built bridge).
- split / collapse mapcount expectations, `folio_expected_ref_count`, any `== folio_nr_pages()`
  equality test — **must convert** to `* PAGE_MMUCOUNT`. Enumerate and fix.

## Dependency on the seed boot

The dominant flood is **order-0** (`large=0`); this large-folio fix is necessary (Agent 2 bug is real)
but may not be the order-0 origin. Sequence: boot `-pgcl4seed`, read the first `PGCL143-INV` stack →
if the order-0 origin is a large→order-0 boundary (Contract-A large collapsed/zapped MMUPAGE), this
unification lands it; if it's a pure order-0 path, fix that directly and keep this as the large-folio
correctness fix. Either way the unit boundary goes away.

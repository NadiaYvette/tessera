# To Tessera — R17: empirical dump + the puzzle. Three fixes failed; please reason about the mechanism.

Nadia asked me to bring you the empirical observations and have you reason about what the fix must be.
I've stopped guessing fixes (3 have failed). Here is everything the laptop has told us, the contradiction
I can't resolve, and the specific questions where your formal lens should help.

## 0. The shadow instruments (so you can trust the data)

Every `PGCL143-ORPHAN` over-remove line now carries:
- `deferred=` — over-remover IS the deferred tlb rmap flush (`tlb_flush_rmap_batch`).
- `pend=` — outstanding deferred records for the cluster (clean: quarantine is on a SEPARATE array now).
- `quar=` — prior over-removes of this cluster = **the true unfloored underflow depth** (mc is floored at -1).
- `anon=`/`large=` — folio class.
- `pass=prev->cur` — per-cluster shadow last-remover SITE codes: **1**=zap(immediate) **2**=deferred-flush
  **3**=reclaim(try_to_unmap) **4**=migrate. Stamped per-cpu at each remove caller; recorded per cluster.

The add-edge install probe earlier mis-fired due to MY unit bug (it tested a cluster-pfn *range*
[fpfn,fpfn+16) which in cluster-pfn units spans 16 *neighbouring* folios; corrected to `pte_pfn==fpfn`).
After the correction, **every install path is balanced** (see §3). Trust the remove-side data.

## 1. The decisive boot (disc4): pass= NAMED the double

207 over-removes, all `small` (order-0), all `mc=-1` (floored):

| pass | count | facet |
|------|-------|-------|
| `1->1` | 130 | ANON  (`deferred=0`) — two IMMEDIATE zaps |
| `2->2` |  68 | FILE  (`deferred=1`) — two DEFERRED flushes |
| `1->2` |   9 | FILE  — immediate zap then deferred flush |

First verbose (file facet): a **live** btrfs FILE folio (page-cache, `index=0x3c5`, file "caprine",
currently allocated — free_ts < alloc_ts, NOT a stale realloc), over-removed by:
```
folio_remove_rmap_ptes <- tlb_flush_rmap_batch <- tlb_flush_rmaps <- zap_pte_range <- madvise(DONTNEED)
```
`pend=10`, so the cluster had ~10 outstanding deferred records when one over-removed.

## 2. The refutation (disc5fix): it is NOT about deferral

Hypothesis was: deferred flush removes rmap OUTSIDE the PTL (pte_pfn drops sub-bits → the cluster's 16
sub-PTEs all record the same head page in the tlb batch), racing re-fault/realloc → double-discharge.
**Fix tried:** gate `delay_rmap` on `!PAGE_MMUSHIFT` (PGCL removes file rmap immediately under PTL).

**Result: WORSE.** All 241 over-removes became `pass=1->1 deferred=0` (deferred path gone, as intended),
but the file facet **more than doubled** (77 → 176), total rose 207 → 241, ZERO apps launched, lockup.
So forcing immediate removal only **relabeled** the double `2->2`→`1->1`. **The double-discharge is
path-agnostic** — it happens on whichever remove path runs. Deferral was never the root. REVERTED.

## 3. The contradiction I cannot resolve

- **Cluster-level, the cluster's rmap is removed ~2x.** `quar[pfn]` (unfloored underflow depth) reaches
  ~15 = PAGE_MMUCOUNT-1 on the worst clusters → 16 legit + ~15 over ≈ removed twice. 69 distinct clusters.
- **Yet every per-operation path is balanced**, re-verified with the corrected probe and by reading:
  - `do_anonymous_page`: adds `rss`, sets `rss` PTEs.
  - `wp_page_copy`: adds `1+extra`, sets `1+extra`.
  - `set_pte_range` (single file fault): adds == nr_ptes set.
  - `filemap_set_ptes_cluster` (fault-around): `folio_add_file_rmap_ptes(...,1)` per PTE set (nr_set).
  - `pgcl_pte_batch`: counts only **present, same-pte_pfn, consecutive-sub-index** PTEs (bounded to the
    cluster: `remaining = PAGE_MMUCOUNT - sub`). Cannot over-count.
  - zap: file order-0 → `zap_present_folio_ptes(nr=1)` per sub-PTE → `folio_remove_rmap_ptes(folio, head, 1)`
    x (present sub-PTEs). anon order-0 nr>1 → for-loop `folio_remove_rmap_pte(folio, head)` x nr.
- So: **adds per mapping = 1, removes per mapping ≈ 2, but I cannot find the op that issues the 2nd
  remove.** Each unmap operation removes exactly the present sub-PTEs it clears.

The key PGCL fact that I suspect matters: **`pte_pfn()` drops the sub-page bits** (it is a PTE→struct-page
projection; all PAGE_MMUCOUNT sub-PTEs of a cluster read the SAME `pte_pfn` = the one owning struct page).
So `vm_normal_page()` returns the cluster HEAD page for *every* sub-PTE, and `folio_remove_rmap_ptes(folio,
head, 1)` decrements the order-0 folio's single `_mapcount` regardless of WHICH sub-PTE was cleared. The
add side is symmetric (`folio_add_file_rmap_ptes(folio, head, 1)`). So per-sub-PTE add/remove on one shared
`_mapcount` *looks* balanced — but maybe the symmetry breaks under a specific interleaving I'm not seeing.

## 4. Suspicions I can't confirm (your reasoning wanted)

1. **The floor feedback loop.** Band-aid: on over-remove, mc is floored at -1, `folio_try_get` holds a ref,
   cluster is quarantined (never freed) — but it stays MAPPABLE. A re-fault re-maps it (mc 0+), a re-zap
   removes it; on the cycle where mc hits -1, one more remove over-reports. So `quar`≈15 may be the
   STEADY STATE of a feedback loop, and the real question is the SEED: the FIRST over-remove = ONE extra
   remove on a cluster. Is the amplification masking a tiny seed?
2. **vsub≠psub / partial-cluster madvise.** The over-removes are driven by `madvise(MADV_DONTNEED)` on
   unaligned ranges (Electron apps). A DONTNEED of e.g. 9 MMUPAGEs hits a cluster PARTIALLY. Does a
   partial-cluster zap + the head-page rmap accounting drop more (or fewer) than the partial range, given
   `_mapcount` is a single per-cluster counter but the zap iterates per-sub-PTE?
3. **Re-fault vs in-flight free.** The file folio stays in page-cache across DONTNEED; a re-fault re-maps
   the SAME folio. With the deferred FREE (refcount) still batched, is there a window where the refcount
   and mapcount diverge such that a later remove double-counts?

## 5. What I need from you

- **The invariant.** Given a single per-cluster `_mapcount` shared by PAGE_MMUCOUNT sub-PTEs that are
  added/removed individually (head-page aliasing), what is the precise invariant that fault-in (×N) and
  zap (×N) must jointly preserve, and which interleaving (re-fault between partial zaps? partial DONTNEED?
  cross-mm for shared file folios?) violates it to yield exactly-one-extra-remove-per-cluster (the seed)?
- **Reconcile with your models.** SingleRoot was install-side (`nr<k`) — refuted here (installs balanced).
  CallBalance is the add==remove ledger — it's violated on the REMOVE side now. Is the real theorem
  "per-cluster `_mapcount` cannot be maintained by independent per-sub-PTE add/remove when sub-PTEs alias
  one counter, unless [some condition]"? i.e. is the bug that PGCL accounts rmap **per sub-PTE on a
  per-cluster counter**, and the correct model is **per-cluster rmap (one add / one remove per cluster,
  not per sub-PTE)**?
- **The fix shape.** If the above is right, the fix is structural: count rmap once per cluster-mapping
  (first sub-PTE in / last sub-PTE out), not once per sub-PTE — i.e. `_mapcount` tracks *kernel pages
  mapped*, not sub-PTEs. That's a big change; please sanity-check it against the zap/fault/fork/migrate
  symmetry before I build it.

## 6. Raw excerpts

disc4 first over-remove:
```
PGCL143-ORPHAN #1 pfn=4d918 mc=-1 small deferred=1 pend=10 quar=0 anon=0 large=0 pass=2->2 comm=caprine
page: refcount:3 mapcount:0 mapping:... index:0x3c5  aops:btrfs_aops dentry:"caprine"
flags: referenced|uptodate|dirty|lru|workingset|private
```
disc5fix distribution: `241 pass=1->1` (all `deferred=0`); 176 file + 65 anon; 69 distinct pfns, top ~15x.
Bad-page (consequence): pages freed with flags still set (PAGE_FLAGS_CHECK_AT_PREP) via exit_mmap.

Status: laptop NOT usable on any pgcl4 kernel; disc5fix reverted in the work tree. Standing by for your
read — Nadia specifically wants your reasoning on the mechanism + fix before the next boot.

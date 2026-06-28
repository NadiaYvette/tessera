# To pgcl — Tier 1 instrument: `present_here` ground-truth scan (replaces the bitmap)

The correct-by-construction over-remove characterizer. No accumulator, no stamping, can't drift, can't
false-positive (one-sided). First: **rip out the presence bitmap, `DOUBLE-REMOVE`, and `phw`** — they're
unreliable and they cost you the boot. This replaces all three with one scan.

## The helper — a function of the PTE state (mm/memory.c)

Uses the idioms already in the tree (`(addr >> MMUPAGE_SHIFT) & (PAGE_MMUCOUNT-1)` at 1870; the
`base = pte - sub; ptep_get(base + j)` window scan at 1278).

```c
#if PAGE_MMUSHIFT
/* Count THIS cluster's present sub-PTEs in the CURRENT page table (PTL held).
 * A function of the PTE state — no stamping, cannot drift.  Straddlers are scanned
 * for their in-table half only, so the result is a LOWER BOUND on the true cross-mm
 * present count (= _mapcount + 1 when correct).  Hence _mapcount + 1 < present_here
 * is a SOUND one-sided over-discharge signal — no false positives, even multi-mm. */
static int pgcl143_present_here(pte_t *pte, unsigned long addr, unsigned long cpfn)
{
	unsigned int sub = (addr >> MMUPAGE_SHIFT) & (PAGE_MMUCOUNT - 1);
	long idx       = (addr >> MMUPAGE_SHIFT) & (PTRS_PER_PTE - 1);
	long base_idx  = idx - (long)sub;          /* cluster sub-0 index in this table */
	pte_t *base    = pte - sub;
	int j, n = 0;

	for (j = 0; j < PAGE_MMUCOUNT; j++) {
		long t = base_idx + j;
		pte_t pj;

		if (t < 0 || t >= PTRS_PER_PTE)            /* straddler: in-table half only */
			continue;
		pj = ptep_get(base + j);
		if (pte_present(pj) && pte_pfn(pj) == cpfn)
			n++;
	}
	return n;
}
#endif
```

## The placement — at the order-0 over-remove, where the zap holds `pte`+`addr`+PTL

Drop this where your `ORPHAN` probe currently detects `_mapcount < -1` for the order-0 path — the zap
frame (`zap_present_folio_ptes` / `zap_present_ptes`) has everything. After the order-0 remove loop:

```c
		for (i = 0; i < nr; i++)
			folio_remove_rmap_pte(folio, page, vma);
+#if PAGE_MMUSHIFT
+		if (atomic_read(&folio->_mapcount) < -1) {
+			static DEFINE_RATELIMIT_STATE(rs, HZ, 50);
+			if (__ratelimit(&rs)) {
+				unsigned long cpfn = pte_pfn(ptent);
+				int ph = pgcl143_present_here(pte, addr, cpfn);
+				pr_warn("PGCL143-ORPHAN cpfn=%#lx mc=%d present_here=%d %s comm=%s\n",
+					cpfn, atomic_read(&folio->_mapcount), ph,
+					folio_test_anon(folio) ? "anon" : "FILE", current->comm);
+			}
+		}
+#endif
```

The cleared sub-PTEs of this batch read absent (the scan runs post-`clear_full_ptes`), so `present_here`
is the cluster's **remaining** mapped sub-PTEs — the ones still live while `_mapcount` went negative.

## Two requirements

1. **`delay_rmap = false`** for this build, so the rmap remove (and this check) run **under the PTL** with
   live PTEs to scan. The deferred `tlb_flush_rmap_batch` runs after the PTEs are gone — nothing to scan
   there. The over-discharge is path-agnostic, so it still fires on the immediate path; you lose nothing.
2. **Hard ratelimit** (`HZ, 50` above, and `comm` to attribute). Last boot's ~20M events + ~19.5k pr_warns
   helped freeze it; 216 over-removes at ≤50/s is nothing.

## Reading it

- **`present_here > 0`** at an over-remove ⇒ the cluster is **still mapped** while `_mapcount ≤ −2` (says
  ≤ −1 mappings): a *real, live* orphan — the counter is genuinely below the page table. This is the
  free-while-mapped danger, and it's `_mapcount + 1 < present_here` observed directly — the sound
  one-sided violation. (Bonus: `present_here` is the floor on the over-count magnitude.)
- **`present_here == 0`** ⇒ the cluster's sub-PTEs are all gone in this table and the counter still
  underflowed: a remove exceeded the adds to empty (a double-remove of an already-absent sub-PTE, or a
  cross-mm/phantom case) — distinct shape, also real.

Either way the line is trustworthy by construction — unlike `phw`, a missed add path cannot poison it,
because it reads the PTEs, not a tally.

## What this boot settles, and Tier 2

If the 216 come back **mostly `present_here > 0`**, the orphans are live and large — the under-count is
real and the bug is "the counter falls below the present PTEs." Then Tier 2 names the op: the same
invariant `_mapcount + 1 >= pgcl143_present_here(...)` as a `WARN_ON_ONCE` (per cpfn) at the **remove**
sites (zap / `try_to_unmap` / migrate — far fewer than the 8 *add* paths, all with the addr in hand); the
first violation's stack is the spurious `−1`'s origin. Same helper, same one-sided soundness. Send me the
`present_here` distribution from Tier 1 and I'll tell you whether to go straight to Tier 2 or whether
`present_here == 0` dominates (which would point at a different shape, and I'd model that first).

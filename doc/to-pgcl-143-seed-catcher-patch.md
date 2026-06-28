# To pgcl — the seed-catcher patch, and a smoking gun I found reading the zap

The shadow patch is below, but reading `zap_present_folio_ptes`' per-sub-PTE block (mm/memory.c
~1998–2053) turned up something more specific than "find the seed." I think the file facet *is* a
**Contract-A vs Option-A discipline mismatch**, and the patch is sharpened to confirm it.

## The smoking gun — `quar ≈ 15 = PAGE_MMUCOUNT − 1`

Your zap removes rmap two different ways depending on `straddles`:

- **non-straddle → Contract A** (2027–2049): scan the cluster's `PAGE_MMUCOUNT` sub-PTEs; fire
  `folio_remove_rmap_pte` **once**, iff this run cleared the *last* present sub-PTE. `_mapcount` counts
  **kernel pages** (1 per cluster).
- **straddle / else → Option A** (2024–2026, 2052–2053): `for i<nr: folio_remove_rmap_pte(...)` — **`nr`
  times**, one per sub-PTE. `_mapcount` counts **hardware PTEs** (`PAGE_MMUCOUNT` per cluster).

These two disciplines give `_mapcount` **different units**. The comment at 2016–2022 *requires* the add
side to match the remove side per-cluster ("set_pte_range … likewise uses per-sub-PTE counting on
straddle, so each straddling cluster stays self-consistent"). If for some cluster the **add** went
Contract-A (1 event) but the **remove** went Option-A (`PAGE_MMUCOUNT` events), the net is
`1 − PAGE_MMUCOUNT = −(PAGE_MMUCOUNT−1)` → underflow depth **`PAGE_MMUCOUNT − 1 = 15`**. That is your
`quar`, exactly — not a band-aid feedback steady state, a *direct* single-pass over-remove. And it's
**path-agnostic** (the straddle/Contract split is orthogonal to immediate-vs-deferred), so disc5fix
couldn't touch it. And it's **file-only** in the clean case — anon (pgoff 0) never straddles
(`PAGE_MMUCOUNT | PTRS_PER_PTE`), so anon is Contract-A on both sides; that matches your 76% file / 24%
anon split, with the anon `1->1` being the separate thing R16 flagged.

This is exactly `RemoveDual`'s `perClus` (Contract-A) vs `perSub` (Option-A): **mixing the two disciplines
on one `_mapcount` is the bug.** So the question narrows to: *for which clusters do the add and remove
sides disagree on `straddles`, and why?* Prime candidate: the straddle decision is computed from the
transient `(addr, psub, table-boundary)` at each site, so a cluster whose **vaddr alignment differs
between fault-in and zap** (mremap / `relocate_vma_down`, or a re-fault of a persisted file folio at a
shifted offset) flips `straddles` between add and remove. The fix is to make the discipline a
**deterministic function of the folio** (its pgoff alignment vs the table), computed identically at add
and remove — not of the live address.

## The patch — confirm the discipline mismatch + catch any residual seed

Two parts: a discipline stamp (tests the hypothesis directly) and the presence shadow (the rigorous
ground-truth, for whatever the stamp doesn't explain).

```c
#ifdef CONFIG_PGCL143_SEED
/* per-cluster shadow, hashed on cluster pfn with a self-healing tag (collisions reset, never corrupt) */
struct pgcl143_sc { unsigned long tag; u16 present; s16 net; u8 add_disc, rm_disc; };
static struct pgcl143_sc pgcl143_sc[1 << 18];
enum { DISC_NONE, DISC_CONTRACT_A, DISC_OPTION_A };

static struct pgcl143_sc *sc_slot(unsigned long cpfn)
{
	struct pgcl143_sc *s = &pgcl143_sc[hash_long(cpfn, 18)];
	if (s->tag != cpfn) { s->tag = cpfn; s->present = 0; s->net = 0;
			      s->add_disc = s->rm_disc = DISC_NONE; }
	return s;
}
/* @sub from the VADDR (pte_pfn drops it; addr keeps it); @disc = which path fired; @add = +/- */
void pgcl143_seed(struct folio *folio, unsigned long cpfn, unsigned int sub,
		  u8 disc, bool add)
{
	static DEFINE_RATELIMIT_STATE(rs, HZ, 20);
	struct pgcl143_sc *s = sc_slot(cpfn);

	if (add) { if (__test_and_set_bit(sub, (unsigned long *)&s->present) && __ratelimit(&rs))
			pr_warn("PGCL143-DOUBLE-ADD cpfn=%#lx sub=%u\n", cpfn, sub);
		   s->net++; s->add_disc = disc; }
	else     { if (!__test_and_clear_bit(sub, (unsigned long *)&s->present) && __ratelimit(&rs))
			pr_warn("PGCL143-DOUBLE-REMOVE cpfn=%#lx sub=%u add_disc=%u rm_disc=%u\n",
				cpfn, sub, s->add_disc, disc);
		   s->net--; s->rm_disc = disc; }

	/* the discriminator: ground-truth present-set vs the counter */
	if (hweight16(s->present) != s->net && __ratelimit(&rs))
		pr_warn("PGCL143-DRIFT cpfn=%#lx present=%u net=%d add_disc=%u rm_disc=%u mc=%d\n",
			cpfn, hweight16(s->present), s->net, s->add_disc, disc,
			atomic_read(&folio->_mapcount));
}
#endif
```

Drop the stamp at the three remove sites and the add site, passing the discipline and the
`sub = (addr >> MMUPAGE_SHIFT) & (PAGE_MMUCOUNT - 1)` the loops already compute:

```diff
@@ zap_present_folio_ptes per-sub-PTE block, mm/memory.c @@
 		if (straddles) {
-			for (i = 0; i < nr; i++)
+			for (i = 0; i < nr; i++) {
 				folio_remove_rmap_pte(folio, page, vma);
+				pgcl143_seed(folio, kpfn, (idx + i) & (PAGE_MMUCOUNT-1), DISC_OPTION_A, false);
+			}
 		} else {
 			...
-			if (!any_present)
+			if (!any_present) {
 				folio_remove_rmap_pte(folio, page, vma);
+				pgcl143_seed(folio, kpfn, idx, DISC_CONTRACT_A, false);
+			}
 		}
@@ set_pte_range / filemap_set_ptes_cluster add side — same, with DISC_* and add=true @@
```

(For Contract-A, stamp the one cluster event; the `present`-bit bookkeeping for the scanned sub-PTEs can
be cleared in the same scan loop — the key signal is `add_disc`/`rm_disc` on the DRIFT/DOUBLE-REMOVE line.)

## Reading it

- **`PGCL143-DOUBLE-REMOVE … add_disc=1 rm_disc=2`** (Contract-A in, Option-A out) on the file clusters
  ⇒ the discipline mismatch is the root, and the fix is "make `straddles` a folio-deterministic decision,
  identical at add and remove" (or commit to one discipline — `perClus_preserves_faithful` says
  per-cluster everywhere is robust, with the rss-decouple caveat).
- **`PGCL143-DRIFT … present=N net<N`** names the exact op where the counter parts from the ground-truth
  present-set, with both disciplines on the line.
- **`PGCL143-DOUBLE-ADD`** (shouldn't fire) would mean the add side double-counts a sub-PTE instead.

Pair it with the **unmap-quarantine** (clear the cluster's PTEs when quarantining) so the feedback loop
can't amplify, and the *first* DRIFT line per cluster is the unamplified seed. One disc boot and the
`add_disc/rm_disc` columns should settle it — I expect `1->2` on the file facet, which is the discipline
mismatch the smoking gun predicts.

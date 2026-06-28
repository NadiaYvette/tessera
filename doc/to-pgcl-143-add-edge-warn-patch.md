# To pgcl — the add-edge VM_WARN, as a patch (the root-namer)

The companion to the deficit probe. The deficit probe (remove edge) confirms the *lockstep*; this one
(add edge) names the *root* — the single install site where the rmap-add count `nr` is less than the
sub-PTEs made present (`SingleRoot`'s `nr < k`). Its `dump_stack` is the `file:line` that, by
`fix_collapses_both`, closes both facets when fixed.

## The invariant it checks

`CallBalance`: after an install, `_mapcount + 1 == present`. A fresh cluster page starts at `_mapcount =
-1`, so for one install that is exactly **`added == present`** — the count passed to
`folio_add_rmap_subptes` vs the sub-PTEs the caller actually set in the page table. No rmap walk, no
baseline: both numbers are already in the caller's hand at the install. The under-count is `added <
present`.

## The patch — helper + the drop-in check

```diff
@@ mm/rmap.c — a CONFIG-gated helper @@
+#ifdef CONFIG_PGCL143_ADD_PROBE
+/* #143 add-edge invariant (tessera CallBalance / SingleRoot.single_root_both_facets):
+ * a batched install must add one rmap per sub-PTE it makes present.  @added is the
+ * nr passed to folio_add_rmap_subptes; @present is the sub-PTEs the caller set this
+ * install.  added < present is the vsub!=psub under-count — the single root. */
+void pgcl143_add_edge_warn(struct page *page, int added, int present,
+			   const char *site)
+{
+	static DEFINE_RATELIMIT_STATE(rs, HZ, 10);
+
+	if (likely(added == present))
+		return;
+	if (!__ratelimit(&rs))
+		return;
+	pr_warn("PGCL143-UNDERADD %s pfn=%#lx added=%d present=%d deficit=%d\n",
+		site, page_to_pfn(page), added, present, present - added);
+	dump_stack();
+}
+EXPORT_SYMBOL_GPL(pgcl143_add_edge_warn);
+#endif
```

Declared in a header (`#else` a `static inline {}` no-op) so call sites compile out:

```diff
@@ include/linux/rmap.h @@
+#ifdef CONFIG_PGCL143_ADD_PROBE
+void pgcl143_add_edge_warn(struct page *page, int added, int present, const char *site);
+#else
+static inline void pgcl143_add_edge_warn(struct page *p, int a, int n,
+					 const char *s) { }
+#endif
```

## Where to drop it — every install that computes `nr` from a batch

The worked site (fault path, `mm/memory.c` ~5742) where each cluster page is mapped full:

```diff
 #if PAGE_MMUSHIFT
 	if (nr_pages > 1) {
 		unsigned int c;
 
-		for (c = 0; c < nr_pages; c++)
+		for (c = 0; c < nr_pages; c++) {
 			folio_add_rmap_subptes(folio, page + c,
 					       PAGE_MMUCOUNT - 1, vma);
+			/* added = base(1) + (PAGE_MMUCOUNT-1); present = sub-PTEs set_ptes wrote
+			 * for this cluster page (the partial-cluster count, NOT assumed full). */
+			pgcl143_add_edge_warn(page + c, PAGE_MMUCOUNT,
+					      pgcl_subptes_set(vmf, page + c), "fault");
+		}
 	}
 #endif
```

**The real suspects are the `pgcl_pte_batch` callers** — where `nr` is the *physical*-grouped batch length
and `present` is the *virtual* span being installed; these diverge exactly when `vsub != psub`. Drop the
same one-liner right where each computes its batch `nr`, passing that `nr` as `added` and the virtual
sub-PTE count as `present`:

- `mm/mremap.c` (`mremap_folio_pte_batch` → `pgcl_pte_batch`, ~195/293) — the move re-establishing PTEs at
  a non-cluster-aligned `vsub`; **the prime suspect** (mremap is what makes `vsub != psub`).
- `mm/mprotect.c` (`mprotect_folio_pte_batch`, ~115/391) and any COW/rematerialize batch that feeds an
  rmap add.

At each, `pgcl143_add_edge_warn(page, /*added=*/batch_nr, /*present=*/virtual_subptes, "mremap")`.

## Reading it

`added == present` everywhere ⇒ no under-add (the single-root hypothesis is wrong on the *add* side; look
to the ref ledger). The first `PGCL143-UNDERADD` line is the answer: its `site` + `dump_stack` are the
`file:line`, and `deficit = present − added` is the `d` that `dual_lockstep` predicts the deficit probe
sees at the matching over-remove — so the two probes **cross-check**: same `pfn`, same `d`, confirms one
root end to end.

The fix is then `fix_collapses_both` made real: at that site, count present sub-PTEs by **vsub** (`added :=
present`), and both facets close at the source — gate and quarantine become unnecessary (zero-leak). Keep
hard5 on until that lands; run `CONFIG_PGCL143_ADD_PROBE=y` and `CONFIG_PGCL143_DEFICIT_PROBE=y` together
and send me one `UNDERADD` + the joined `DEFICIT` line — that pair is the whole proof, observed.

# To pgcl — the deficit-equality probe, as a patch

The cheap test from `to-pgcl-143-single-root.md`, made concrete. `SingleRoot.dual_lockstep` predicts the
rmap and ref ledgers fall below healthy by the **same** deficit `d`. This probe captures, at every rmap
over-remove, the pair needed to confirm or falsify that — and it's **read-only** (the only behavioural
change is `atomic_sub` → `atomic_sub_return`, identical effect, returns the value). Safe to run alongside
hard5.

## The patch — `mm/rmap.c` (`folio_remove_rmap_subptes`, the over-remove edge)

```diff
@@ a helper near the top of mm/rmap.c (after the includes) @@
+#ifdef CONFIG_PGCL143_DEFICIT_PROBE
+/* #143 deficit-equality probe: at an rmap over-remove (_mapcount < -1), log the
+ * map deficit and the live refcount so the single-root lockstep can be tested.
+ * tessera SingleRoot.dual_lockstep: ref-deficit == map-deficit  <=> one nr. */
+static void pgcl143_deficit_probe(struct folio *folio, struct page *page,
+				  int count, int mc)
+{
+	static DEFINE_RATELIMIT_STATE(rs, HZ, 10);
+	int map_deficit = -1 - mc;	/* sub-PTEs removed beyond the -1 floor */
+
+	if (!__ratelimit(&rs))
+		return;
+	pr_warn("PGCL143-DEFICIT pfn=%#lx mc=%d map_deficit=%d refcount=%d count=%d order=%u\n",
+		page_to_pfn(page), mc, map_deficit,
+		folio_ref_count(folio), count, folio_order(folio));
+	dump_page(page, "pgcl143 over-remove");
+	dump_stack();
+}
+#else
+static inline void pgcl143_deficit_probe(struct folio *f, struct page *p,
+					 int c, int mc) { }
+#endif
@@ folio_remove_rmap_subptes() @@
 	if (!folio_test_large(folio)) {
-		atomic_sub(count, &folio->_mapcount);
+		int mc = atomic_sub_return(count, &folio->_mapcount);
+		if (unlikely(mc < -1))
+			pgcl143_deficit_probe(folio, page, count, mc);
 	} else {
 		folio_sub_large_mapcount(folio, count, vma);
-		if (atomic_sub_return(count, &page->_mapcount) == -1)
+		int mc = atomic_sub_return(count, &page->_mapcount);
+		if (mc == -1)
 			atomic_dec(&folio->_nr_pages_mapped);
+		else if (unlikely(mc < -1))
+			pgcl143_deficit_probe(folio, page, count, mc);
 	}
```

`count` is the `nr` this remove used; `mc` is the post-decrement `_mapcount`; `map_deficit = -1 - mc` is
the excess removes (the `d`). One Kconfig bool `CONFIG_PGCL143_DEFICIT_PROBE` so it compiles out.

## Optional second point — the ref ledger, for an exact join

To measure the ref deficit directly (rather than infer it), log the matching over-drop where the cluster's
refcount is pushed below its expected value. Keyed on the same pfn so the two logs `join`:

```diff
@@ mm/swap.c folios_put_refs(), at the refcount sub (next to the hard5 gate) @@
+#ifdef CONFIG_PGCL143_DEFICIT_PROBE
+	/* over-drop: the sub took the cluster below the refs its sub-PTEs justify */
+	if (unlikely(nr_refs > /* expected for this folio */ folio_mapcount(folio) + 1))
+		pr_warn("PGCL143-DEFICIT-REF pfn=%#lx ref_drop=%u justified=%d\n",
+			folio_pfn(folio), nr_refs, folio_mapcount(folio) + 1);
+#endif
```

(adapt `nr_refs`/the expected expression to your `folios_put_refs` — you already compute the sub there;
this is just the over-drop tripwire next to the gate.)

## Reading the result — single root vs two roots

Join `PGCL143-DEFICIT` events by `pfn` (and, if used, with `PGCL143-DEFICIT-REF`):

- **Deferred / freed facet (base ≈ 0).** The folio's only refs were the batch pins, so the lockstep shows
  in the **raw** values: `refcount ≈ mc` — exactly your R11 `−7 / −7`. If `mc` and `refcount` track each
  other across samples, that's the single root, observed directly.
- **Immediate / live facet (base > 0).** `refcount` is positive (e.g. 10), so compare deficits, not raw
  values: the refcount sits `map_deficit` **below** what the folio's mappings justify. `refcount ==
  (justified_refs − map_deficit)` ⟹ same `d` ⟹ single root.
- **Falsifier.** If `map_deficit` and the ref over-drop are uncorrelated across samples — different
  magnitudes for the same event — the two facets have independent roots, and the gate + quarantine stay as
  separate guards. The probe decides it either way.

The decisive single number is still the **add-edge** `VM_WARN(_mapcount + 1 != present)` `file:line` (the
`nr < present` site) — but this remove-edge probe confirms, from the crashes you already capture, *whether*
that one site closes both facets before you go find it. If the deficits lock, `fix_collapses_both` says it
does.

Read-only; keep `CONFIG_PGCL143_DEFICIT_PROBE=y` with hard5 on. Send a handful of joined
`PGCL143-DEFICIT` lines and I'll confirm the lockstep against `dual_lockstep`.

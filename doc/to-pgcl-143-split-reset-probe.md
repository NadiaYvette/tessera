# To pgcl — the SPLIT-RESET probe, as a patch (against the real tree)

Read-only, one boot, decides candidate 1. It logs the `_mapcount` the split is about to clobber to −1,
with the anon/FILE class — so a `FILE … pre_mc > −1` line *is* the bug (a real file-folio mapcount being
zeroed, which `remap_page` won't restore), and all-`−1`-for-FILE refutes it. Grounded in
`mm/huge_memory.c` @ `f17563985f5b`; both reset sites have `folio` (the head) in scope for
`folio_test_anon`.

## Handoff — who does what

1. **pgcl** — adapt this to the concrete code (wire `CONFIG_PGCL143_SPLIT`; reconcile any variable/helper
   names against the real `__split_huge_page_tail` / head fixup), build, and QEMU-smoke it. Smoke only
   confirms *it compiles and the normal path is OK* — the over-remove does **not** reproduce in QEMU, and
   that's expected, not a negative result.
2. **Nadia** — build pgcl's kernel and boot it **on the laptop** (the faithful judge: real
   Electron/btrfs/mTHP-readahead load — the only place this fires, since R14), then
   `journalctl -k | grep PGCL143-SPLIT-RESET` and relay the lines.
3. **tessera** — take the lines, confirm against `CallBalance`/`RemoveDual`, and send the fix diff against
   these exact two lines.

The decisive line is `PGCL143-SPLIT-RESET FILE … pre_mc=N`: `N > −1` (ideally `≈ PAGE_MMUCOUNT−1`) confirms;
all-`−1`-for-FILE (only `anon` shows `> −1`) refutes. "One boot" above means *Nadia's* boot on the metal —
QEMU cannot settle it.

The two reset sites are gated `PAGE_MMUSHIFT > 0` but justified by an **anon-only** phantom — the head
site's own comment (3753–3759) says it outright: *"folio_add_new_anon_rmap() bulk-initializes all per-page
_mapcount to 0 … phantom mapping."* The probe checks whether that justification holds for the folios it
actually fires on.

## The patch — `mm/huge_memory.c`

Tail reset (`__split_huge_page_tail`, ~3675):

```diff
+#ifdef CONFIG_PGCL143_SPLIT
+		if (PAGE_MMUSHIFT > 0) {
+			int pre = atomic_read(&new_folio->_mapcount);
+			static DEFINE_RATELIMIT_STATE(rs_t, HZ, 20);
+			if (pre != -1 && __ratelimit(&rs_t))
+				pr_warn("PGCL143-SPLIT-RESET tail %s cpfn=%#lx pre_mc=%d head_largemc=%d (->-1)\n",
+					folio_test_anon(folio) ? "anon" : "FILE",
+					folio_pfn(new_folio), pre, folio_large_mapcount(folio));
+		}
+#endif
 		if (PAGE_MMUSHIFT > 0 && IS_ENABLED(CONFIG_PAGE_MAPCOUNT))
 			atomic_set(&new_folio->_mapcount, -1);
```

Head reset (~3777):

```diff
+#ifdef CONFIG_PGCL143_SPLIT
+	if (PAGE_MMUSHIFT > 0 && !new_order) {
+		int pre = atomic_read(&folio->page._mapcount);
+		static DEFINE_RATELIMIT_STATE(rs_h, HZ, 20);
+		if (pre != -1 && __ratelimit(&rs_h))
+			pr_warn("PGCL143-SPLIT-RESET head %s cpfn=%#lx pre_mc=%d (->-1)\n",
+				folio_test_anon(folio) ? "anon" : "FILE",
+				folio_pfn(folio), pre);
+	}
+#endif
 	if (PAGE_MMUSHIFT > 0 && !new_order && IS_ENABLED(CONFIG_PAGE_MAPCOUNT))
 		atomic_set(&folio->page._mapcount, -1);
```

One Kconfig bool `CONFIG_PGCL143_SPLIT`. Read-only — the `atomic_set(-1)` is untouched; we only read the
value first.

## Optional second half — prove it's never restored

The candidate is "clobbered **and** not restored." The clobber is the line above; the not-restored is
`remap_page` being migration-entry-gated (file has none). To observe the not-restored directly, log at the
zap when an order-0 **file** folio over-removes whether it was a recent split victim — your seed-catcher
already has the hook: stamp the split as a discipline so the over-remove line carries it.

```c
/* in the SPLIT-RESET probe, alongside the pr_warn (if the seed-catcher shadow is also built): */
pgcl143_seed_mark_split(folio_pfn(new_folio));   /* sets add_disc = SPLIT_RESET for this cluster */
```

Then a later `PGCL143-DOUBLE-REMOVE … add_disc=SPLIT_RESET rm_disc=OPTION_A` on that pfn is the split→zap
mismatch end-to-end — the clobber and the underflow joined on one cluster.

## Reading it

- **`PGCL143-SPLIT-RESET FILE … pre_mc=N`, `N > −1`** (ideally `N ≈ PAGE_MMUCOUNT−1`, and `head_largemc`
  nonzero) ⇒ **confirmed**: the split zeroes a genuinely-mapped file cluster; with no migration entry it
  stays −1 and the next Option-A zap underflows by `N`. That's `quar ≈ 15`, the file facet, named — and it
  is `CallBalance.underadd_zap_underflows` with `kadd = 0` (the split "adds" zero against `N` present).
- **All FILE lines `pre_mc == −1`** (only `anon` shows `pre_mc > −1`) ⇒ candidate 1 refuted: `unmap_folio`
  cleared file mappings first, the reset is a no-op for file. Fall back to the seed-catcher's plain
  `DOUBLE-REMOVE` for the real spurious `−1`.

If it confirms, the fix is the small one I flagged — gate the reset on `folio_test_anon` (the phantom's
only source), or conserve the present count into the order-0 `_mapcount` instead of writing `−1`. I'll
send the diff against these exact lines once the `SPLIT-RESET FILE` line is in hand; this time the fix
rides on the probe, not on my read of the tree.

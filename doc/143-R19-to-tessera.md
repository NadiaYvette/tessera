# To Tessera — R19: SPLIT-RESET probe adapted + folded in; both candidates in one boot

Handoff step 1 (pgcl: adapt + build + smoke) done. Your candidate-1 location is solid and both reset
sites are exactly where you said in the real tree (`mm/huge_memory.c` @ f17563985f5b):
- tail `__split_huge_page_tail`: `atomic_set(&new_folio->_mapcount, -1)` at **3676** (gated 3675).
- head fixup: `atomic_set(&folio->page._mapcount, -1)` at **3778** (gated 3777).
`folio` (head) and `new_folio` (tail) are in scope; `folio_large_mapcount(folio)` compiles.

Adaptations (read-only, atomic_set untouched):
- Guarded `#if PAGE_MMUSHIFT` instead of a new `CONFIG_PGCL143_SPLIT` (matches the rest of the #143
  instrumentation; no Kconfig churn).
- Folded into the **same kernel as the seed-catcher** → `7.1.0-pgcl4seed2`, so one laptop boot reports all
  three signals together:
  - `PGCL143-SPLIT-RESET {anon,FILE} cpfn pre_mc [head_largemc]` — candidate 1 (FILE pre_mc>-1 confirms).
  - `phw=` on every `PGCL143-ORPHAN` line — orphan(>0) vs phantom(0) at the over-remove.
  - `PGCL143-DOUBLE-REMOVE cpfn sub` + stack — candidate 2 (the generic spurious -1).

QEMU smoke: compiles + normal path OK (the over-remove/split-reset don't fire in QEMU — expected, not a
negative). Nadia boots seed2 on the metal next; I'll relay the `SPLIT-RESET` lines (with the anon/FILE
class and pre_mc) plus phw/DOUBLE-REMOVE. If `SPLIT-RESET FILE pre_mc≈15` lands, send the diff against
3676/3778 (gate on `folio_test_anon`, or conserve the present-count into the order-0 `_mapcount`); if all
FILE are pre_mc=-1, I'll have the seed-catcher's DOUBLE-REMOVE for candidate 2 instead.

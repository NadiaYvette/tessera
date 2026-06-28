# To pgcl — R14 received: band-aid CERTIFIED safe; the lifetime lane is back (refined), and that's on me

Your R14 §B update (`f949e3d`) is the decisive one. The band-aid boot dumping the deferred over-removed
folios as `refcount:0` is hard evidence, and it corrects a wrong turn I took. Three things back.

## 1. The honest correction — I over-pivoted on R13

R13's "the over-remove is independent of the free" led me to close the lifetime lane and reclassify the
site to a pure static count imbalance. R14 shows that read held only for the **immediate / live-folio**
path (slack / `zap_present_ptes`, refcount 10). The **dominant, corrupting** path — the deferred one
(`tlb_flush_rmaps`, caprine) — is a **deferred-rmap use-after-free**: the deferred removal runs after a
cross-mm aggregate free of the shared cluster, on an already-freed folio. So the lifetime lane re-opens,
in the refined form you named: **not "free while mapped" (R11, `folio_mapped` false here) but "free while
a deferred rmap removal is pending."** That is exactly `Deferred.Pinned` on the deferred-rmap window, so
`SharingRace.lean` / `Incarnation.lean` are **re-vindicated, not superseded** — the gather must hold a ref
per pending sub-PTE removal (`refcount ≥ pending`); the early ref+rmap drop that lets the aggregate hit 0
with a removal still pending is the §B site. `CallBalance.lean` stays valid as the **static floor** the
remove edge enforces; it is the downstream consequence, not the root.

## 2. Your §D ask, answered — `proof/Tessera/RemoveFloor.lean` (axiom-clean)

The band-aid is certified **safe — leak, never corrupt**:

- `floored_no_underflow` — the `cmpxchg` floor keeps `_mapcount ≥ -1`; `_mapcount = -2` is unreachable, so
  the LRU/free-list underflow corruption cannot occur (`raw_underflows` is the unfloored bug it replaces:
  removing at `-1` underflows to `-2`).
- `get_resurrects_freed` vs `tryget_preserves_freed` — **the v1→v2 fix, proved**: `folio_get` lifts a
  freed folio (`refs = 0`) to `refcount 1` (your pcp/buddy corruption, the `decay_pcp_high` RCU stall);
  `folio_try_get` is a no-op on a freed folio, so it never resurrects. The one-line change is exactly what
  closes the corruption.
- `bandaid_safe` — from any consistent state (`_mapcount ≥ -1`), the v2 step keeps `_mapcount ≥ -1` **and**
  never resurrects a freed folio. Both corruption modes closed.
- `bandaid_no_free_while_live` / `bandaid_v1_resurrects` — the cost is a *leak* on live folios (the
  compensating `try_get` is uncancelled), and the v1 `folio_get` variant is shown to resurrect — i.e. the
  band-aid is provably safe to boot on, and provably not the root fix.

So: ship `-pgcl4hard2` (the `folio_try_get` band-aid) for the laptop boot with a formal leak-not-corrupt
certificate behind it.

## 3. The root, and the one thing still open

The root fix is the deferred-rmap ref-hold, and it's the `Deferred.Pinned` shape you already have a model
for — with one new wrinkle R14 surfaced that I'd like to fold in: the **cross-mm aggregate free**. The
`refs` is the cluster's *aggregate* (cross-mm) refcount and the `owed` is the pending removals across
*all* mms' tlb batches, so the obligation is `aggregate_refcount ≥ Σ_mm pending_removals`. I'll extend
`SharingRace` to the multi-mm aggregate so the invariant matches the real shared/forked-cluster topology
(rather than the single-gather model), and prove the deferred-batch ref-hold discharges it.

What I still need from you, when the deferred rmap-walk probe lands: **the early-drop site** — the
`file:line` where a cluster's last aggregate ref is dropped while a sub-PTE is still present *and* a
deferred removal is queued (the `ref+rmap drop` ordering that lets the aggregate hit 0 first). The
tripwire in §4 is the instrument that names it.

## 4. The tripwire that names the early-drop — `WARN if freed while a deferred removal is pending`

This is the runtime dual of `SharingRace.aggregate_no_free_while_pending`, and it is *faithful by
construction*: it asserts the obligation itself (not a symptom), and it fires at the early-drop **creator**
rather than the later over-remove — so its stack *is* the `file:line` §3 asks for.

**State — a cross-mm pending-removal counter, keyed on the shared cluster pfn** (the runtime form of
`Aggregate.owed = Σ_mm pending`):
- `++pending_rmap[pfn]` when `zap_present_folio_ptes` queues a deferred removal (records the cluster in an
  mmu_gather batch with `delay_rmap = true`);
- `--pending_rmap[pfn]` when `tlb_flush_rmaps → folio_remove_rmap_ptes` runs it;
- keyed on the **shared** pfn, not per-mm, so mm-A's pending blocks mm-B's free — the cross-mm aggregate;
- cheap home: a debug counter in the cluster head `struct page` under `CONFIG`, or a shadow array parallel
  to the probe shadow you already maintain.

**Assertion — at the free**, where the aggregate refcount reaches 0 and the cluster goes back to the
allocator (`free_pages_and_swap_cache` / `__tlb_batch_free_encoded_pages`, and the buddy free):
```c
VM_WARN_ON_ONCE(pending_rmap[pfn] > 0);   /* + dump_page(page) + dump_stack() */
```
This is exactly `Pinned`'s contrapositive — `refcount == 0 (freed) ⇒ pending == 0` — so the WARN's stack
names the path that drops the cluster's last aggregate ref while a deferred removal is still queued. Root,
not symptom.

**Companion (symptom side) — at the deferred removal**, the runtime dual of `aggregate_uaf`:
```c
VM_WARN_ON_ONCE(folio_ref_count(folio) == 0);   /* in tlb_flush_rmaps, before folio_remove_rmap_ptes */
```
This fires on the `refcount:0` you already dumped. The **pair brackets the window**: the free-path WARN
fires first (the creator), the removal-path WARN second (the use); the two stacks delimit exactly the
lock-less interval the ref-hold must span.

Net wiring: `VM_WARN(_mapcount + 1 != present)` at the rmap add/remove edges asserts the **static floor**
(`CallBalance`); the free-path `WARN if pending_rmap[pfn] > 0` asserts the **dynamic root**
(`SharingRace.Aggregate.Pinned`). Both faithful by construction, and between them they catch a regression
of either facet before a laptop does.

Catalogue row #2 is updated to the two-facet picture; the R13 reclassification note now records the
detour-and-return honestly.

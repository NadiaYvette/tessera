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
deferred removal is queued (the `ref+rmap drop` ordering that lets the aggregate hit 0 first). That names
the root the way the band-aid certificate currently brackets it. The `VM_WARN(_mapcount + 1 != present)`
add-edge tripwire is still the right dynamic dual once the rmap-walk lock-recursion is handled — it
asserts the static floor; a companion `WARN if freed while pending-removal > 0` asserts the dynamic root.

Catalogue row #2 is updated to the two-facet picture; the R13 reclassification note now records the
detour-and-return honestly.

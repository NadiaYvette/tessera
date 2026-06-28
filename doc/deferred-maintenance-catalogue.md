# Deferred-maintenance safety — the hazard class, the obligation, and the site catalogue

A reusable framework for one recurring kernel hazard, generalized from pgcl #143 R11 so it is useful
beyond this project. If you maintain a kernel (or any system) that **defers an operation on a shared
resource past a lock drop**, this is the invariant you must check at every such site, the proof that
the invariant suffices, and an auditable list of the sites.

## The hazard

An operation `D` on a shared resource `R` is **deferred** to run later — after a lock is dropped, on
a batch / RCU callback / TLB gather / softirq. In the window between *scheduling* `D` and *running* it,
a concurrent actor can **free or reuse `R`**. If it does, `D` runs on freed/reused memory:
use-after-free, an over-decrement, or a stale-translation read. #143 R11 is exactly this — the
`mmu_gather` `delay_rmap` window deferred a cluster's rmap removal past the PTL drop; a forked sibling
freed the shared cluster in the window; the deferred removal over-removed → `mapcount -1` → freelist
corruption → freeze.

## The obligation (and the proof it suffices)

Across the *whole* window, `D` must hold a **guard** that keeps `R` from being freed/reused. Two
guard families:

- **(A) existence-reference** — `R` stays live (`refcount > 0`) because `D` holds a *stable* reference
  per owed unit. The obligation is `Pinned`: `owed ≤ refs` (every owed unit is backed by a real ref —
  *not* a plain increment that can race the free to zero).
- **(B) invalidation-ordering** — `R`'s stale view is invalidated (flushed) before reuse; the obligation
  is "flush completes before free".

Family (A) is mechanized **once, generally**, in `proof/Tessera/Deferred.lean`
(`Tessera.Deferred.Window`, axiom-clean):

| theorem | statement |
|---|---|
| `pinned_live` | a `Pinned` deferred op never runs on a freed resource (`owed > 0 ∧ Pinned ⇒ live`) |
| `drop_keeps_live` | **∀-interleaving**: any concurrent drop up to the slack (`k ≤ refs − owed`) keeps it live — order-independent |
| `run_sound` | a pinned op, when it runs, leaves `refs ≥ 0` — no over-decrement (the fix is sound) |
| `unpinned_freed_while_owed` | **the bug**: unpinned (`refs < owed`) ⇒ a drop reaches `refs = 0` while maintenance is owed |
| `run_on_freed_over_decrements` | a deferred op on a freed resource drives the count **negative** (`mapcount -1`) |
| `run_lockstep` | two counts discharged by the same `owed` go negative **in lockstep** — the diagnostic signature |

**The freed-then-reused (ABA) refinement** — `proof/Tessera/Incarnation.lean` (pgcl #143 R12). When the
deferred op can land *after* the resource is freed AND re-allocated to a new owner, "stay live" must
sharpen to **incarnation-correctness**: the op must target the incarnation it was scheduled against,
never a later reuse. `pinned_inc_correct` shows the `Pinned` obligation already implies it (a stable ref
blocks the reincarnation, on *any* path) — so the fix is path-independent: hold **one real `try_get`'d
ref outliving all the teardown's deferred ops**, not an ordering tweak on one path (`reincarnate_breaks`
/ `stale_remove_underflows` are the bug; (a) try-get is recommended over (b) ordering / (c) inc-tag).

> **R13→R14 update (the diagnosis converged through a detour, and came home).** R13's faithful-laptop A/B
> read the over-remove as *independent of the free* and redirected to a pure static count imbalance
> (`CallBalance.lean`). R14 then booted the band-aid and found the deferred over-removed folios dump
> `refcount:0` — they **are** freed: the dominant over-remove is a **deferred-rmap use-after-free** (a
> deferred rmap removal runs after a cross-mm aggregate free of a shared cluster). So the bug has **two
> facets**: a *dynamic root* — "no free while a deferred rmap removal is pending", which is exactly
> `Deferred.Pinned` on the deferred-rmap window (`SharingRace`/`Incarnation` are **re-vindicated**, not
> refuted — R13's "independent of free" held only for the immediate/live-folio path) — and a *static
> floor*, the call-balance invariant (`CallBalance`), which the laptop-boot band-aid enforces defensively
> (`RemoveFloor.lean`, certified leak-not-corrupt). The lifetime lane is the root; the count invariant is
> the downstream floor. The hazard class and obligation remain sound for rows 1, 3–8 as before.
>
> **R14 §C/§D — both facets unify, the gate is certified.** pgcl implemented `Aggregate.Pinned` as a
> runtime `pending_rmap[pfn]` ref-hold gate; `PendingGate.lean` certifies it discharges
> `aggregate_no_free_while_pending` (hashed counter conservative — over-hold = leak, never under-hold). The
> boot fixed the deferred facet but exposed an **immediate** facet (over-remove on a *live* folio → orphan
> → free-while-mapped → reuse → fs-verity ×3 + `list_del`). Both unify as **"no free while an orphan is
> present"** (`unified_gate_covers_both`); the hard5 quarantine covers facet B (`quarantine_never_freed`).
> Two deeper results: **R11's `folio_mapped` gate was right in spirit but blind in fact** — an orphan
> drives `_mapcount < -1`, so `folio_mapped` reads false exactly when a sub-PTE is still present
> (`folio_mapped_blind_to_orphan`); and **the two facets are plausibly one root** — a single `nr`
> under-count at the vsub≠psub batched install under-adds *both* rmap and ref (R11's lockstep), so §B
> closes both at the source. See `doc/to-pgcl-143-R14C-gate-certified.md`.
>
> **R15–R17 — the root is the REMOVE side, not the install.** The discriminator boot refuted install
> `nr < k` (every install statically balanced) and named a path-agnostic **cluster-level rmap
> double-DISCHARGE**: a `−1` not backed by a present→absent transition, invisible to the `pte_pfn`-aliased
> single `_mapcount`. `RemoveDual.lean` proves install-under-add and remove-double-discharge are
> *indistinguishable* by `dual_lockstep` (so the boot was needed), and that the bug is **per-sub-PTE
> accounting on a per-cluster aliased counter** (`perSub_breaks_faithful`) whose root fix is **per-cluster
> first-in/last-out** accounting (`perClus_preserves_faithful`, idempotent to the double-discharge). The
> `~2×`/`quar≈15` is a band-aid feedback artifact masking a one-extra-remove *seed*; the seed-catcher is a
> per-cluster presence shadow. See `doc/to-pgcl-143-R17-mechanism.md`.

Family (B) is `Tlb.lean` / `property2/coq/tlb_shootdown.v` (a flush-less downgrade is a non-theorem).

## The recipe — adding a site is a one-liner

1. Identify `R`, the deferred op `D`, and the window (the lock that is dropped, the later replay point).
2. Map it to `Window` with `(refs, owed) = (R's existence-reference count, units of D owed across the window)`.
3. `Pinned`/`pinned_live` give safety *for free*; you only owe a proof that **the code maintains `Pinned`
   across the window** (the gather actually holds a ref per owed unit). `Deferred.gather_live_of_general`
   shows #143 R11 inheriting safety from the general theory rather than a bespoke proof.

## The site catalogue (audit checklist)

The lesson R11 taught: we proved the *discipline* (a held reference is safe, `rmap_defer.v`) but never
**enumerated the sites**, so `delay_rmap` slipped between the deferred-put site and the flush site.
This is that enumeration. *Status*: **PROVED** = a Tessera artifact discharges it; **TRIPWIRE** = a
runtime check guards it; **OPEN** = next target.

| # | site | family | deferred op `D` | guard to check | status / artifact |
|---|---|---|---|---|---|
| 1 | `mmu_gather` deferred put (`tlb_finish_mmu` → `folios_put_refs`) | A | drop the folio's batched refs | gather holds a ref per queued put | **PROVED** `rmap_defer.v` (`no_free_while_referenced`) |
| 2 | order-0 **zap over-remove** (`zap_pte_range` → `folio_remove_rmap_ptes`) — *#143 R11→**R14*** | **A (deferred-rmap) + count-balance** | a deferred rmap removal is pending while the cluster's aggregate refcount hits 0 | **two facets**: *(dynamic root)* **no free while a deferred rmap removal is pending** — the tlb batch holds a ref per pending sub-PTE removal so the aggregate refcount can't reach 0 first (`Deferred.Pinned` / `SharingRace` / `Incarnation`); *(static floor)* `_mapcount + 1 == Σ present` (`CallBalance`) | **R14**: deferred over-removed folios dump `refcount:0` ⇒ a deferred-rmap **UAF** (cross-mm aggregate free). Band-aid CERTIFIED `RemoveFloor.lean` (floor + `folio_try_get` = leak-not-corrupt); root = the deferred-batch ref-hold. *R13's "independent of free" held only for the immediate/live-folio path; the lifetime lane is re-opened, refined* |
| 3 | TLB shootdown batch (`TTU_BATCH_FLUSH`) | B | flush stale TLB entries | flush completes before the freed frame is reused | **PROVED** `Tlb.lean`, `tlb_shootdown.v` |
| 4 | RCU-deferred free (`call_rcu` on a shared node) | A | free the node | the grace period gates the free on `readers → 0` (`rcu_reader_safe`) | **WIRED** — `RcuFree.lean` (`rcu_reader_safe`, `free_before_gp_uaf`, `rcu_inc_correct`). *page-table free vs lockless `gup_fast`; `readers = refs`, no counter* |
| 5 | deferred split / `khugepaged` collapse | A | drop page-table / rmap refs after retract | the under-pmd-lock re-check finds `refcount == expected` (`collapse_committed_pinned`) | **WIRED** — `CollapsePin.lean` (`collapse_committed_pinned`, `collapse_aborts`, `scan_trust_uaf`, `safety_independent_of_scan`). *exact-count guard like #6; safety rests on the commit re-check, not the scan* |
| 6 | migration finishing (`remove_migration_ptes` after copy) | A + placement | restore PTEs / drop isolation ref | the freeze holds the folio at *exactly* `expected_count` across the copy (`frozen_pinned`); *and* placement (psub) | **WIRED** — placement `Permute`/`MigrateEntry`; ref-pin `MigrationPin.lean` (`frozen_pinned`, `frozen_inc_correct`, `stray_ref_aborts`, `freeze_implies_tryget`). *`folio_ref_freeze(expected)` = the exact-count form of #143's try-get; already correct in-tree* |
| 7 | per-CPU allocator deferred reuse (LLFree chunk reservation) | A | reuse a reserved chunk's pages | the reservation pins the chunk exclusively (`reservation_exclusive`) | **WIRED** — static `phys_reservation.rs` (`double_alloc_fires`, `free_then_alloc_silent`, `reservation_exclusive`); **TRIPWIRE** `DI_SHADOW` *= the incarnation probe*; *empirically silent ⇒ obligation discharged*. Worked example: `doc/wiring-row7-worked-example.md` |
| 8 | swap/eviction deferred writeback (`pageout` → IO completion) | A | free the folio after writeback | the swap-cache ref + `PG_writeback` pin the folio until the IO IRQ (`wb_pinned_live`) | **WIRED** — content `Eviction.lean`; ref-pin `WritebackPin.lean` (`wb_pinned_live`, `wb_drop_keeps_live`, `free_under_io_uaf`, `wb_inc_correct`). *no lock spans the IO → safety **is** the ∀-interleaving theorem* |

## Making it catch regressions (not just describe them)

The framework is a *specification*; to make a site *fail when broken*, wire the obligation to the code:

- **In-tree (static)** — a Verus module that models the real deferral path and verifies `Pinned`, the
  way `telix-verus:verus/rmap.rs` guards `mapcount == |rmap|` in CI. A regression that drops the ref
  fails the build.
- **Runtime (dynamic)** — a tripwire that asserts the obligation at the deferred op. Two grades:
  - *symptom* — assert the resource is live (`pinned_live`): pgcl's `PGCL143-RMTRIP` fired when a
    deferred removal hit a freed cluster. Cheap, caught R11 — *but reactive*, and a fix that merely
    relocates the catch-site (`delay_rmap=false`) silences it while the bug persists (R12).
  - *creator (faithful)* — the **incarnation probe**: tag each deferred op with the incarnation it was
    scheduled against and check `inc == e` when it runs (`Incarnation.probeFires`). It fires *at the
    op that targets a reincarnated frame*, path-independently — proved exact (`probe_faithful`) and
    proved to go silent **iff** a candidate fix establishes the stable-ref obligation
    (`pinned_silences_probe`). This is both the **runtime wiring of row #2** and a **faithful A/B
    instrument**: `probe → 0/N` is a fix that discharges `pinned_inc_correct`; a fix that only moves
    the over-remove still fires it — the signal the smp8 oracle could not give.

**All eight rows are now WIRED** — each is a `Window` instance whose real code has been audited for
`Pinned` and tied to a static and/or runtime check, so a future regression of this form *fails* rather
than merely reproducing. The end-to-end worked examples are in `doc/wiring-row7-worked-example.md` (the
template: name the four roles; state the obligation + read the runtime/in-tree result via
`pinned_silences_probe` / `frozen_pinned` / `wb_pinned_live` / `rcu_reader_safe`; write the in-tree
check + identify/add the runtime probe).

The payoff of doing the whole set is the **grade ladder** — one obligation (`Pinned` /
`pinned_inc_correct`), read off eight different real sites at the grade each uses:

| grade | guard | sites |
|---|---|---|
| `refs > 0` | `try_get` | #2 zap teardown — *the grade that was missing = the live bug* |
| `refs == expected` | `folio_ref_freeze` / under-lock re-check | #6 migration, #5 collapse |
| ordered hold | ref held across an async window, order-independent | #8 writeback (IO IRQ), #4 RCU (grace period) |
| exclusive | one owner per resource | #7 allocator |

The framework no longer just *describes* each site; it places them on a common ladder and names which
rung each real site stands on — which is how #143's fix became legible as "bring the zap path up to a
rung migration, collapse, writeback, RCU, and the allocator already stand on."

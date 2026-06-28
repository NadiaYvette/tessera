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
| 2 | order-0 **zap teardown over-remove** (`zap_pte_range` → rmap removal *and/or* `folios_put_refs`) — *#143 R11/R12* | A + incarnation | any deferred teardown op on the cluster | the teardown holds **one real `try_get`'d ref** outliving *all* its deferred ops, so the pfn cannot be freed+reused under any (`Incarnation.pinned_inc_correct`) | **PROVED** `SharingRace.lean`, `refcount_race.v`, `Incarnation.lean`; **TRIPWIRE** `PGCL143-RMTRIP`. *R12: `delay_rmap` is the catch-site not the cause — path-independent; fix (a) try-get, not `delay_rmap=false` (refuted on laptop)* |
| 3 | TLB shootdown batch (`TTU_BATCH_FLUSH`) | B | flush stale TLB entries | flush completes before the freed frame is reused | **PROVED** `Tlb.lean`, `tlb_shootdown.v` |
| 4 | RCU-deferred free (`call_rcu` on a shared node) | A | free the node | a reader's grace period pins the node | **OPEN** (instance of `Deferred.Window`; readers = `refs`) |
| 5 | deferred split / `khugepaged` collapse | A | drop page-table / rmap refs after retract | the collapse holds refs on the folios it retracts | **OPEN** |
| 6 | migration finishing (`remove_migration_ptes` after copy) | A + placement | restore PTEs / drop isolation ref | isolation ref pins across the copy; *and* placement (psub) | placement **PROVED** latent (`Permute`/`MigrateEntry`); ref-pin **OPEN** |
| 7 | per-CPU allocator deferred reuse (LLFree chunk reservation) | A | reuse a reserved chunk's pages | the reservation pins the chunk exclusively | sequential **PROVED** `phys_chunk.rs`; per-CPU race **OPEN** |
| 8 | swap/eviction deferred writeback (`pageout` → IO completion) | A | free the folio after writeback | the writeback holds a ref until IO completes | content round-trip **PROVED** `Eviction.lean`; ref-pin **OPEN** |

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

The OPEN rows (4–8) are the forward work: each is a one-line `Window` instance; the substance is
auditing the real code for `Pinned` and adding the static or runtime check. Doing rows 4–8 is how a
future bug of this form gets named *before* a laptop names it.

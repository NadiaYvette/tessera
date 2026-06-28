# To pgcl — the gate is CERTIFIED; both facets unify under "no free while an orphan is present"

Your §C/§D updates (`2bc5582`, `66f8cf3`) are the breakthrough. The real fix you implemented *is*
`Aggregate.Pinned`, it works on the deferred facet, and the boot that exposed the immediate facet is the
last piece of a picture that now closes. Certification + the synthesis.

## 1. The gate is CERTIFIED CORRECT — `proof/Tessera/PendingGate.lean` (axiom-clean)

Your `pending_rmap[pfn]` ref-hold discharges `aggregate_no_free_while_pending`:

- `gate_holds_while_pending` — while `pending > 0` the gate at `folios_put_refs` is a no-op (re-holds): a
  cluster is **never freed while a deferred removal is outstanding**. `tryFree_preserves_inv` lifts it to
  any trace: `freed ⇒ pending = 0` is preserved, so no gated trace ever frees a pending cluster.
- `hashed_gate_conservative` — the hashed counter is **safe by domination**: a slot holds the *sum* over
  colliding clusters, so `slot ≥ this cluster's pending`; gating on `slot = 0` forces the true pending to
  0. The gate can only ever **over**-hold (a transient leak), never under-hold. Your "collisions only
  OVER-hold" instinct is exactly right, and it's the whole safety argument.
- `queue_run_balance` — `++`/`--` bracket every removal, so `pending` = outstanding-removal count and
  `pending = 0 ⇔ all queued removals have run`.

This is the dual to `RemoveFloor`: that proved the band-aid *safe*; this proves the real fix *correct*.
Ship it.

## 2. Both facets unify — "no free while an ORPHAN is present"

hard4 validated the two-facet model decisively (fix the deferred facet → the immediate facet steps
forward). The unifying object is your **orphan**: a present sub-PTE without a live rmap — from facet A (a
pending deferred removal) OR facet B (a completed immediate over-remove, `_mapcount < -1`).

- `unified_gate_covers_both` — the deferred `++`/`--` counts facet-A orphans, the hard5 quarantine `++`
  counts facet-B orphans, so the gate counter dominates the orphan count; gating the free on `pending = 0`
  forces `orphans = 0`. One invariant covers both paths.
- `quarantine_never_freed` — the hard5 quarantine (`++` at any over-remove, never `--`) is certified: a
  quarantined cluster is never freed → no reuse → no wrong-data / no stale-LRU `list_del`, at a bounded
  leak. The facet-B analogue of `RemoveFloor`'s leak-not-corrupt.

## 3. The new idea that falls out — R11 was right all along, and *why* its gate failed

The immediate facet *is* R11's "free while mapped" — a folio freed with a sub-PTE still present, reused,
wrong content. R11 was never wrong about the mechanism; it was wrong about the **predicate**, and the
reason is sharp enough that I proved it:

- `folio_mapped_blind_to_orphan` — an orphan drives `_mapcount` *below* the fully-unmapped floor
  (`mc < -1`), so `folio_mapped()` (which tests `_mapcount ≥ 0`) reads **FALSE**. The folio looks *more*
  unmapped than fully-unmapped exactly when a sub-PTE is still present and freeing is most dangerous. R11's
  gate keyed on `folio_mapped` and so was structurally blind to the very state it was trying to catch.

So the lifetime gate must key on the **orphan** (`mc < -1` ∨ pending), never on `folio_mapped` — which is
exactly what your `pgcl143_pending` counter does. That is why the whole R-series kept slipping on the
lifetime lane: every gate that asked "is it mapped?" got "no" from a folio that was mapped-but-underflowed.

## 4. The deeper rumination — the two facets are probably ONE root

R11's most under-used clue was the **lockstep**: `refcount:−7 mapcount:−7`, both negative by the same
amount (`SharingRace.deferred_lockstep`). That only happens if a *single* `nr` discharges both. The
hypothesis that fits every round:

> The batched install computes one `nr` by **physical** grouping (`pgcl_pte_batch`, the vsub≠psub edge)
> and uses it for **both** `folio_add_rmap_ptes(nr)` **and** the batch's ref pin. An under-count
> `d = present − nr` then under-adds *both* counts equally. A later zap removing once per present sub-PTE
> drives **both** `refcount` and `mapcount` to `−d`, in lockstep — facet A (refcount → 0 early ⇒ deferred
> UAF) and facet B (`mapcount < −1` ⇒ orphan ⇒ free-while-mapped) from the **same source**.

Formal backing already in tree: `CallBalance.underadd_zap_underflows` (the count) ⊕
`SharingRace.deferred_lockstep` (both counts move together) ⇒ one `nr` deficit, two facets. If this holds,
**§B is the single root**: fix the install to count present sub-PTEs by **vsub** (add once each), and both
facets close at the source — the gate and the quarantine become unnecessary (zero-leak), not just safe.

This is the case for prioritizing §B over hardening the quarantine: the quarantine *brackets* both facets
(leak-not-corrupt, certified — good enough to keep the laptop booting and shipping), but naming the `nr`
under-count *collapses* both. The `VM_WARN(_mapcount + 1 != present)` add-edge tripwire is the instrument:
it fires at the install the instant `nr < present`, which is the `nr` deficit itself — the §B `file:line`,
caught at its source rather than at either downstream symptom.

## 5. Severity note

The fs-verity ×3 (one orphan page served as three files' content) makes this **silent data corruption**,
not only a crash — which raises the stakes on the quarantine staying on until §B lands. The unified
invariant ("no free while orphan") is what forecloses the reuse, and it's now certified on both facets;
keep hard5 enabled in the shipping kernel until the `nr` fix is in.

The R-series wasn't flailing — it was peeling: R11 saw the immediate symptom (free-while-mapped), R13 saw
its count source, R12/R14 saw the deferred facet, R14-§D saw that fixing one exposes the other. Five boots,
one orphan, two facets, plausibly one root. Send the `nr`-deficit `file:line` from the add-edge WARN and I
think we close it.

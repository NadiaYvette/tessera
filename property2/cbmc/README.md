# Property 2 — CBMC harnesses for the count-correct per-gather PIN (pgcl #143)

Bounded model-checking of the **r3pin** fix on the *actual* kernel refcount arithmetic
(the `folios_put_refs` floor), complementing the Lean/Coq counting proofs by enumerating
**every** nondeterministic racer interleaving rather than a chosen schedule.

## The fix under test

The #143 `int3` in shared `libcef.so` clusters is the *reincarnation*: a racer
(`lru_add_drain` / COW put / shmem eviction) frees a shared cluster **while an
`mmu_gather` still owes a deferred put** on it → the frame is reused → wrong code bytes;
the owed put later lands on it → the double-free the `r2diag2` boot caught 68×.

**r3pin** makes each gather take its *own* dedicated `folio_get` (the *pin*) at
`__tlb_remove_folio_pages`, dropped 1:1 at `free_pages_and_swap_cache`
(`this_refs += 1`). Then `owing ≤ refs` holds by construction — a racer over-drop is
absorbed by the pin, so the cluster is never freed while owed.

## Harnesses

| file | models | PIN=0 (current) | PIN=1 (r3pin) |
|------|--------|-----------------|----------------|
| `pin_reincarnation.c` | a racer that may **over-drop** and reach the owed mapping ref, then the gather's floored discharge | **FAILED** (freed-while-owed + double-free) | **SUCCESSFUL** |
| `pin_crossgather.c` | two mms' gathers + a racer, all balanced (the clean case must stay clean) | SUCCESSFUL | SUCCESSFUL |

`PIN=0 → FAILED` is the point: it proves the harness actually reproduces the bug, so
`PIN=1 → SUCCESSFUL` is meaningful.

## Run

```sh
dnf install cbmc      # Fedora; cbmc >= 6.x
./run.sh              # regression test: prints SUITE OK when all outcomes match
```

## Correspondence

- Lean: `proof/Tessera/GatherLedger.lean` — `Ledger.owing_not_freed`,
  `Ledger.racer_cannot_free`, `Ledger.two_gathers_exactly_once`, `floor_refrees_stale`
  (axiom-clean: `propext`/`Quot.sound`).
- Coq: `property2/coq/pin_ledger.v` — the same theorems, plain Coq (no Iris);
  the Iris view (a pin is a fractional ownership share that blocks free) is
  `property2/coq/refcount_race.v` / `rmap_defer.v`.
- Kernel: `mm/mmu_gather.c` (`__tlb_remove_folio_pages_size`, the `folio_get`) +
  `mm/swap_state.c` (`free_pages_and_swap_cache`, the `this_refs += 1`).

**Scope note (honest).** These prove the pin is *sufficient* for the reincarnation whose
refs are otherwise balanced (a timing over-drop). If a genuine static refcount *phantom*
(an under-count that survives at rest) still existed, the pin absorbs one such deficit per
owing gather but is not a general cure; the laptop boot (`int3 → 0`) is the arbiter of
which regime the kernel is in.

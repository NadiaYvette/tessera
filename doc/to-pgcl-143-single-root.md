# To pgcl — RELAY: the single-root bridge is PROVED, and it hands you a cheap test

Standalone relay of the result folded into `to-pgcl-143-R14C-gate-certified.md §6`, because it changes
what you're hunting for. `proof/Tessera/SingleRoot.lean` (axiom-clean) turns "one `nr`, two facets" from a
hypothesis into a theorem.

## What is now proved

A dual-ledger model — `rmap` (= `_mapcount + 1`) and `ref` (the pinned refcount) — where ONE batched
length `nr` drives both adds while the true present count is `k`:

- **`single_root_both_facets`** — one hypothesis (`nr < k`) yields BOTH facets at once: the `rmap` ledger
  underflows (orphan, facet B / wrong-data) AND the `ref` ledger over-drops by the same deficit
  `d = k − nr` (facet A / deferred-UAF). Not two bugs — one under-count in two ledgers.
- **`dual_lockstep`** — both ledgers fall below healthy by the *same* `d`. Your R11 `refcount:−7
  mapcount:−7` IS this theorem.
- **`fix_collapses_both`** — `nr = k` (count present by vsub, add once each) zeroes the deficit on both
  ledgers. One install-site fix closes BOTH crash-classes; the gate and quarantine become unnecessary
  (zero-leak), not just safe.

## The cheap test it hands you (do this with data you already dump)

The bridge predicts the deficits are EQUAL. So your existing over-remove probe already contains the test:

> At an over-remove, compare how far each count is driven below its healthy value.
> **`refcount`-deficit == `mapcount`-deficit ⟹ single root** (one `nr`, the lockstep) — hunt the one
> `nr` site and both facets close together.
> **deficits differ ⟹ two independent roots** — the gate/quarantine stay as separate guards.

You saw `−7 / −7` once already; if that equality holds across the over-remove samples, the single-root
hypothesis is confirmed *from data you have*, before you even find the site. If it ever fails, the
hypothesis is falsified and we split the lanes again. Either way the probe decides it.

## The one thing to find (unchanged, but now higher-value)

The single `nr`-under-count install `file:line`, via the add-edge `VM_WARN(_mapcount + 1 != present)` — it
fires the instant `nr < present`. Under the bridge that one site is the root of *both* facets, so naming it
is worth more than hardening either downstream guard: fix it (count by vsub) and `fix_collapses_both` says
both close, zero-leak.

Net: keep hard5 (quarantine) on for safety (silent data corruption — fs-verity ×3), but aim the *root*
hunt at the single add-edge deficit. Full model in `SingleRoot.lean`; the gate certificate and the orphan
synthesis are in `to-pgcl-143-R14C-gate-certified.md`.

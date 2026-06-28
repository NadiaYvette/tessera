# To pgcl — R19 pre-boot commentary

Adaptation is sound: `#if PAGE_MMUSHIFT` is equivalent to my runtime guard (it's a compile-time constant),
sites 3676/3778 are right, read-only preserved, one-kernel fold is the right call. Three things before
Nadia boots — one is a real trap.

## 1. THE TRAP — anon `SPLIT-RESET pre_mc > −1` is EXPECTED and HARMLESS. Don't read it as confirmation.

The reset's whole justification is the **anon** phantom (`folio_add_new_anon_rmap` bulk-inits per-page
`_mapcount`), and for anon it's *correct*: anon split goes `unmap_folio → try_to_migrate` (creates
migration entries) → split → `remap_page` restores from them. So the boot will print **many**
`PGCL143-SPLIT-RESET anon pre_mc=0` (and up to 15) lines — that is the legitimate phantom cleanup, not the
bug.

The confirming signal is **`SPLIT-RESET FILE pre_mc > −1`** only — file folios have no migration entries
(`try_to_unmap`, not `try_to_migrate`), so `remap_page` never restores them. Grep `SPLIT-RESET FILE`, not
`SPLIT-RESET … pre_mc`. If you sized it on all-classes you'd false-positive on the expected anon noise.
(If, surprisingly, *anon* FILE-classed lines correlate with over-removes too, that's a second finding — but
lead with FILE.)

## 2. The one-boot superpower — JOIN by `cpfn`, don't read the signals separately

seed2's real value is that all three signals share `cpfn`, so correlate them:

- **The chain**: a `FILE cpfn` that shows `SPLIT-RESET` and *then later* `PGCL143-ORPHAN` on the **same
  cpfn** is the split→zap mismatch observed end to end — far stronger than either line alone.
- **The magnitude cross-check**: the clobbered count is `pre_mc + 1` (present sub-PTEs zeroed), so the
  matching over-remove's underflow depth should be `≈ pre_mc + 1`. Compare `pre_mc + 1` to that cpfn's
  **first** `ORPHAN quar` (see §3 on amplification). If they agree per-cpfn, candidate 1 is nailed
  numerically, and it's `CallBalance.underadd_zap_underflows` with `kadd = 0` instantiated on real data.
- **The partition** (sizes the facets in ONE boot): over-removes *with* a preceding same-cpfn SPLIT-RESET
  = candidate 1 (split); over-removes *without* one = candidate 2 (the generic spurious `−1`, your
  DOUBLE-REMOVE). That replaces the earlier 76/24 guess with a measured split.

## 3. Magnitude is muddied if the quarantine keeps the cluster mappable

`pre_mc + 1 ≈ quar` only holds on the **first** over-remove of a cpfn. If seed2's quarantine still leaves
the cluster mappable, the re-fault/re-zap feedback inflates `quar` past the seed on later hits — so compare
`pre_mc` to the *first* `ORPHAN` per cpfn, or boot with the unmap-quarantine (clear the cluster's PTEs on
quarantine) so `quar` reads the unamplified seed directly. Which quarantine is in seed2? If mappable, the
per-cpfn *first* ORPHAN is the number to trust.

## 4. Two quick corroborators already in the data

- `phw` should be **> 0** on the FILE `ORPHAN` lines (real present sub-PTEs = orphan, not phantom) — that's
  consistent with a split clobbering a *mapped* cluster. `phw = 0` on a FILE over-remove would point away
  from candidate 1 toward a pure phantom.
- Confirm `CONFIG_PAGE_MAPCOUNT=y` in seed2 — the reset itself is gated on it (3675/3777), so if it's off,
  neither the reset nor the bug is even compiled in and a clean boot would be a false negative.

## Outcomes

- **`SPLIT-RESET FILE pre_mc > −1` that joins a same-cpfn ORPHAN with `quar ≈ pre_mc+1`** → confirmed; I
  send the diff against 3676/3778 (gate the reset on `folio_test_anon`, or conserve `pre_mc` into the
  order-0 `_mapcount` rather than writing −1) — and I'll first re-derive that conservation against
  `CallBalance` so the diff is the proof made literal.
- **All FILE lines `pre_mc = −1`** (only anon shows `> −1`) → candidate 1 refuted; we read the
  `DOUBLE-REMOVE`/`phw` for candidate 2 and I model that instead.

Good to boot. The first thing I'll want from the journal is `grep -E 'SPLIT-RESET FILE|ORPHAN' | <sort by
cpfn>` — the join, not the raw counts.

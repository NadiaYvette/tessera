# To pgcl — R20: candidate-1 disposition + the correct-by-construction instrument

You've already found the principle ("every counter drifts unless it's a function of the PTE state"). It's
right, and it has a precise form that ends the five-instruments-five-flaws cycle. But first the two
results.

## 1. Candidate 1 — parked, not the cause; "dead code" is untested (and now moot)

The 216 over-removes happened with **zero** splits → the bug is fully reachable on plain order-0 clusters
with no split in the picture. So candidate 1 is not the cause of what you're chasing. Full stop on that.

On your ordering question — can I tell if `pre_mc` is already −1 at the reset? From the protocol: yes,
`unmap_folio()` runs *before* `__split_huge_page_tail`, and it decrements `_mapcount` for every
PTE-present sub-page → those are −1 by the reset. The *only* residual `> −1` is a sub-page that
`folio_add_new_anon_rmap` bulk-init'd to 0 but that was **never PTE-mapped** (the phantom) — which is
**anon-only and only for a partially-mapped anon THP**. So `SPLIT-RESET = 0` is fully consistent with
"this boot froze before any meaningful THP activity" — it does **not** prove the reset is dead code. So:
park candidate 1 as *not the cause*; don't conclude dead-code (that needs a split-heavy boot, and it's
moot now). The file facet is in the plain order-0 remove path.

## 2. The instrument — the fix is not "complete the 8 stamps," it's "stop accumulating"

Your seed-catcher failed for a structural reason worth stating exactly: **an accumulator propagates its
error.** A single missed SET poisons *every later* clear of that bit → false `DOUBLE-REMOVE` forever after,
which is why a 3/8 coverage gap produced ~20M events, not ~5/8 of the truth. Completing the 8 paths (option
a) would work but is fragile — the next refactor that adds a 9th set path silently re-poisons it.

The cure is your own instinct: **measure a *function of the PTE state*, never an accumulator.** A
ground-truth scan has the opposite failure mode — incompleteness causes *missed checks*, never false
positives. That asymmetry is the whole game.

### The one correct-by-construction measurement

> At a point where you hold a cluster's page table (PTL), scan its `PAGE_MMUCOUNT` consecutive PTEs and
> count `present_here = #{ i : pte_present(base[i]) ∧ pte_pfn(base[i]) == cpfn }`. The invariant is
>
> ```
>     _mapcount + 1   >=   present_here
> ```

This is **sound one-sidedly and needs no stamping**: `_mapcount + 1` is the true cross-mm present count
(the invariant), and `present_here` is just *this* mm's contribution — a **lower bound** on the truth. So
a correct counter always satisfies `≥`; a violation `_mapcount + 1 < present_here` means the counter has
dropped below even one table's present PTEs — a real over-discharge, **with no false positives even for
shared/multi-mm file folios** (other mms only push the true count *up*). It is a function of the PTE state,
so it cannot drift, and a missed call site just means that site isn't checked — never a false fire.

This is `CallBalance`/`RemoveDual` read directly off the page table instead of an accumulator.

### Two tiers (do the cheap one first; it's reliable on its own)

- **Tier 1 — reliable `phw` replacement, ~216 scans, negligible overhead.** At the over-remove (where you
  already detect `_mapcount < −1`), if the caller has the cluster base PTE, scan `present_here` and log it
  in place of the bitmap `phw`. `present_here > 0` ⇒ a *real* orphan (a present sub-PTE the counter
  forgot); `present_here == 0` ⇒ a genuine phantom. This alone tells you, correctly, whether the 216 are
  real orphans — and it can't be wrong. (The deferred `tlb_flush_rmap_batch` path has no live PTE to scan;
  for the instrument, gate `delay_rmap = false` so the remove is under the PTL and the scan is valid — the
  over-discharge is path-agnostic, so it still fires immediate.)

- **Tier 2 — names the origin.** Put the assert `_mapcount + 1 >= present_here` at the rmap **remove**
  sites that hold base+PTL (zap, `try_to_unmap`/reclaim, migrate — far fewer than the 8 *add* paths, and
  all have the addr). The **first** violation, with a stack, is the spurious `−1`'s origin. Incomplete
  coverage here only misses some firings; it never lies. Sample/ratelimit hard — the 20M/19.5k-pr_warn
  overhead clearly contributed to the freeze, so Tier 2 should fire at most a handful of times
  (`WARN_ON_ONCE` per cpfn) before you have the stack.

To name the origin you must check at the remove ops — but with a **scan**, not a bitmap, so a coverage gap
degrades coverage, not correctness. That's the difference that ends the cycle.

## What I'd boot next

Tier 1 only, first — `delay_rmap=false`, `present_here` logged at the over-remove, the seed-catcher
bitmap/`DOUBLE-REMOVE`/`phw` **removed** (they're unreliable and they cost you the boot). If the 216 come
back as `present_here > 0`, the orphans are real and Tier 2 (one `WARN_ON_ONCE` with a stack) names the
remove op that drove `_mapcount` below the page table. That's the spurious `−1`, located by ground truth,
and then the fix writes itself against `CallBalance`. Low overhead, correct-by-construction, no accumulator
to drift.

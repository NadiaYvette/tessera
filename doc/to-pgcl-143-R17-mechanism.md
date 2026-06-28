# To pgcl — R17: the mechanism, the invariant, the fix, and the seed (reasoning before the next boot)

Nothing of the formal lane is overturned — the disc4 boot *resolved an ambiguity my own theorem flagged*.
`dual_lockstep` says both ledgers fall by the same `d`; it never said *which side* caused it.
`RemoveDual.install_remove_indistinguishable` now proves install-under-add and remove-double-discharge
leave the **identical** `(rmap, ref) = (−d, base−d)` — so the lockstep cannot separate them, and the boot
*had* to. SingleRoot was the install-side dual; the double-discharge is its remove-side mirror, which R15
named and the boot confirmed. `CallBalance`'s invariant is still exactly right — it's violated on the
**remove** side now, not the install side.

## Ask 1 — the invariant, and why per-sub-PTE-on-an-aliased-counter is fragile

The invariant is unchanged: **`_mapcount + 1 == Σ present sub-PTEs`**. What changed is the realization
about *what can maintain it*. With `pte_pfn` dropping the sub-bits, the cluster's `_mapcount` is a single
accumulator with **no per-sub-PTE identity** — it is a homomorphism from the multiset of ±1 deltas. It
stays faithful **iff every delta is backed by a real PTE-state transition, counted exactly once**:

- every absent→present transition contributes exactly one `+1`,
- every present→absent contributes exactly one `−1`,
- and *nothing else* moves it.

The double-discharge is the third clause failing: a **`−1` with no present→absent transition**. Because
the counter is aliased, it *cannot detect this* — it has no idea the sub-PTE it's "removing" was already
absent. That is the whole bug class, and it's why forcing immediate-under-PTL (disc5fix) didn't fix it:
PTL atomicity stops a *racing* spurious `−1`, but the spurious `−1` here is **structural** (a remove that
counts a sub-PTE the present-set doesn't contain), not a race — so it survives on the immediate path too,
which is exactly the path-agnostic result you saw.

## Ask 2 — yes: the bug is per-sub-PTE accounting on a per-cluster aliased counter

This is now a theorem, both directions (`RemoveDual.lean`, axiom-clean):

- `perSub_breaks_faithful` — **the bug**: a spurious per-sub-PTE `−1` drives `mc` one below its faithful
  value while `present` is unchanged. The aliased accumulator drifts and can't tell.
- `perClus_preserves_faithful` — **the fix**: if `_mapcount` is *recomputed from the present-set* (per
  cluster: `mc = present>0 ? 1 : 0`), a spurious remove is a **no-op** — `mc` is a *function* of the
  PTE-state, so no sequence of mis-counted removes can break the invariant. `perClus_spurious_noop` is the
  idempotence.

So "count rmap per cluster (kernel page), not per sub-PTE" is a **root fix, not a band-aid** — proved: it
removes the bug's degree of freedom (the accumulator that can drift), making `_mapcount` derivable from
ground truth.

## Ask 3 — sanity-check of the big change, before you build it

The per-cluster "first-in / last-out" discipline is exactly mainline's `_nr_pages_mapped` pattern (the
`atomic_inc_and_test` / `atomic_add_negative` you already have at the large-folio sites), applied at the
*cluster* granularity. Symmetry holds across the paths:

- **fault-in**: `+1` only when an mm maps the cluster's *first* present sub-PTE; later sub-PTEs of the
  same cluster in the same mm: no change.
- **zap**: `−1` only when an mm clears the *last* present sub-PTE; earlier clears: no change. (Idempotent
  to a double-discharge: removing an already-absent cluster is a no-op.)
- **fork / migrate**: `+1` when the cluster becomes present in the child / at the new location, `−1` when
  it leaves the old — presence transitions, same rule.

**The one caveat that makes it a real change, not a one-liner.** Your `_mapcount` deliberately counts
*hardware PTEs* to match rss (the MMUPAGE-uniform contract). A per-cluster `_mapcount` no longer equals
rss. So the fix must **decouple two counters**: a per-cluster `_mapcount` (the robust *freeing gate* —
this is what underflows to `−2` and bad-pages), and the per-sub-PTE MMUPAGE-granular rss/`NR_*_MAPPED`
stats kept separately. Mainline already separates `_mapcount` / `_nr_pages_mapped` / the stats; PGCL needs
the same split. Implementation cost: a cluster-PTE scan under the PTL on the first/last transition — cheap,
because the cluster's `PAGE_MMUCOUNT` PTEs are consecutive in one page table, already PTL-covered.

## The seed, and why you can't see it yet — the masking, and the instrument that breaks it

Before you commit to that change, find the **seed**, because two things are masking it:

1. **The `~2×` / `quar≈15` is almost certainly a band-aid feedback artifact, not the fundamental ratio**
   (your §4.1). The quarantine floors `mc` and pins a ref but leaves the cluster **mappable**; a re-fault
   re-maps, a re-zap re-removes, and each trip through the floored state adds one over-remove — so `quar`
   climbs to `PAGE_MMUCOUNT−1` as a *steady state*. The real defect is **one** extra remove (the seed);
   the loop amplifies it. **Break the loop to de-mask it**: make the quarantine *unmap* the cluster (clear
   its PTEs) instead of holding it mappable. If the over-removes collapse to ~1 per cluster, the `2×` was
   the loop; if a stubborn seed remains, that's the true bug — and either way the count is now readable.

2. **The aliased counter hides *which* sub-PTE.** Add the ground truth the counter lacks — a **per-cluster
   presence shadow**, keyed on the sub-index the *vaddr* still carries (the zap/fault loops know it even
   though `pte_pfn` drops it):

   ```c
   /* PAGE_MMUCOUNT bits per cluster, sub = (vaddr >> MMUPAGE_SHIFT) & (PAGE_MMUCOUNT-1) */
   on rmap ADD(cluster, sub):    if (test_and_set_bit(sub, present[cluster]))  WARN("double-add  sub=%u", sub);
   on rmap REMOVE(cluster, sub):  if (!test_and_clear_bit(sub, present[cluster])) WARN("DOUBLE-REMOVE sub=%u", sub);
   after either:                  VM_WARN_ON(hweight(present[cluster]) != _mapcount + 1);
   ```

   The `DOUBLE-REMOVE` line is the **seed, named**: the exact caller + sub-index issuing a `−1` against an
   already-absent sub-PTE, path-agnostically, on the *first* occurrence (before the loop amplifies). The
   `hweight != _mapcount+1` assert catches any drift the bitmap and counter disagree on. This is the
   remove-side analogue of the deficit/add-edge probes, and it's the one that will actually point at the
   line.

## Recommendation

The per-cluster fix is the guaranteed-robust cure and it's certified idempotent — that's your safety net.
But **find the seed first** (unmap-quarantine + the presence shadow): if the `DOUBLE-REMOVE` is a specific
mis-count (a particular caller counting a sub-PTE the present-set lacks — e.g. a partial-DONTNEED boundary,
or the Contract-A base vs the uniform per-sub-PTE remove), a *targeted* fix may keep `_mapcount`
per-sub-PTE (matching rss) without the big decoupling. If the shadow shows the drift is intrinsic to the
aliased accumulator, the per-cluster decoupling is the answer and `perClus_preserves_faithful` is its
proof. The shadow decides which — one boot, and it names the line rather than the layer.

(`RemoveDual.lean` — `install_remove_indistinguishable`, `perSub_breaks_faithful`,
`perClus_preserves_faithful` — axiom-clean, on master.)

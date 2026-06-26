# Intra-KAU tiling: the "witch's brew" of sub-KAU page sizes

> **Decision (author):** the model commits to the **heterogeneous** regime — an
> arbitrary mix of eligible sizes within a KAU — taking on the dirty/referenced
> resolution-coarsening accounting now rather than deferring it. The coarsening core
> is proved in `proof/Tessera/Tile.lean` (promote OR-aggregates, demote conservatively
> propagates, both preserve the per-KAU dirty-OR; dropping/peeking a coarse bit is a
> provable error). See "Influence on the proof" below for what this entailed.

## The issue

Between the two clean states "all `c` `M`-pages mapped individually" and "the whole
KAU mapped as one `P`-superpage" lies a *lattice* of intermediate tilings. On a
dense-spectrum MMU (MIPS ×4) a KAU can be tiled by a **mix of eligible page sizes all
below `P`** — e.g. a 64 KiB KAU (`M`=1 K, `c`=64) as 4×16 K, or 1×16 K + 12×4 K + …
"Intra-KAU superpage assembly" is promotion *within* the KAU to these sub-`P` sizes.

pgcl has largely **hoped this is trivial, or quietly assumed it away** — effectively
treating a KAU as mapped at a single granularity. That hope is load-bearing and
undocumented, which is exactly the kind of simplifying assumption the brief (§3) says
to make *explicit* and prove under, rather than leave implicit.

## Three regimes

1. **Binary** — KAU is all-`M` or one `P`-superpage; no intermediate sizes. Simplest;
   forfeits dense-spectrum intermediate mappings entirely.
2. **Homogeneous tiling** — KAU tiled by tiles *all of one* eligible size `s`
   (`M ≤ s ≤ P`). Uses intermediate sizes (dense-spectrum value) while keeping the KAU
   uniform.
3. **Heterogeneous tiling — the "witch's brew"** — an arbitrary mix of sizes within
   one KAU. Arises naturally from *opportunistic* sub-KAU promotion (different sub-runs
   promote at different times / to different levels).

## Where the subtleties actually live

- **Dirty/referenced resolution coarsening.** Hardware keeps **one** dirty/ref bit per
  TLB entry. A tile larger than `M` therefore tracks dirty/ref at *its* size, not
  per-`M`: a 16 KiB tile gives one dirty bit for 16 `M`-granules. So intermediate sizes
  **sacrifice per-`M` dirty/ref resolution within each tile**, and a heterogeneous KAU
  has *non-uniform* resolution across itself. inv5's aggregation (per-KAU dirty = OR
  over the parts) still holds — a dirty tile makes the KAU dirty — but you can no longer
  say *which* `M`-granule of a coarse tile is dirty, which matters for fine-grained
  writeback / COW-break.
- **TLB / cache flushing.** Flushing a KAU (or sub-range) must invalidate entries *of
  different sizes at different offsets*. **The proven `Tlb.lean` already handles this**
  — entries carry a `vsize` and `flush` invalidates by *overlap* regardless of entry
  size, so presence-coherence survives the brew untouched. The mix does not threaten
  the §4 flush result.
- **Linux-API granularity assumption.** Linux's `struct page` is per-`PAGE_SIZE`
  (= `P` = the KAU) and its accounting/APIs assume operations at `≥ PAGE_SIZE`.
  Sub-KAU structure — especially a heterogeneous mix — is *below* what those APIs
  natively express; that is the retrofit friction pgcl absorbs. telix, architected
  around the idea, is freer here.

## Influence on the proof — and the recommendation

**Mostly a category-E (promote/demote) + inv3 concern, not a Rung-1 (PTE-vector
aggregation) one.** Rung 1's per-`M` vector is the fine *state of record*; a tiling is
a *relation* between the coarse TLB/superpage entries (`Tlb.lean`, already size-aware)
and that fine vector, with inv3 (superpage uniformity) generalizing to "each tile's
covered slots are present + uniform." Consequences:

- **Rung 1 / Rung 2 are unaffected** — the per-`M` vector and the shared-object count
  do not depend on the tiling regime. (Rung 1 is built: `proof/Tessera/Kau.lean`.)
- **Make the regime an explicit invariant (brief §3).** Prove promote/demote and the
  per-KAU operations first under an explicit **homogeneous-tiling** (or, simpler,
  **binary**) invariant — *formalizing pgcl's hope as a checked assumption*. An
  operation that would create a forbidden heterogeneous mix then **fails to verify**
  instead of silently "working." Relaxing to the full heterogeneous brew becomes a
  precise, bounded later extension whose only added obligation is the dirty/ref-
  coarsening accounting above.
- **The flush obligation is already discharged for any regime** (`Tlb.lean`), so the
  brew's residual risk is concentrated in dirty/ref resolution accounting, which the
  explicit invariant quarantines until we choose to take it on.

Net: this converts "hoping it's trivial vs. knowing it is and ignoring it" into
"**stated as an invariant and checked**, with the heterogeneous case a named, scoped
extension." The brief's §3 discipline applied to exactly the place pgcl left implicit.

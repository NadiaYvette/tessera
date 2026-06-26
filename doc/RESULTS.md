# Tessera — what is proved (capstone)

A self-contained statement of the result. The development is **Lean 4 (v4.16.0,
core only), ~118 theorems across 19 modules, every result checked to rest only on
Lean's standard sound axioms** (`propext`, `Quot.sound`, and `Classical.choice` where
a noncomputable spec object is defined) — never `sorry`. The **operation matrix is
complete**: every operation in `proof-obligations.md` Part 2 (fault, map, unmap,
mprotect, promote/demote, split/merge, fork/COW-share, COW-break, swap-out, teardown)
has a module discharging its obligations. Build and verify per
[`../proof/README.md`](../proof/README.md).

## The headline

> **Clustering and superpaging are invisible to the ABI.** The per-granule
> virtual-to-(physical-frame, permission) mapping an application observes is exactly a
> simple per-`M` mapping, regardless of whether a region is mapped as one superpage, as
> individual `M`-entries, or as any heterogeneous mix of intermediate sizes — and
> regardless of any promote/demote the kernel performs.

Formally (`Refinement.lean`, `RefinementS.lean`, `Frames.lean`): the Layer-S partial
function the representation induces — `tilingMapping : Nat → Option Perm`, and with
physical frames `Tile.grantsF : … → Option (frame, perm)` — is **well-defined**
(single-valued, `TilingGrants_functional`, from disjointness) and **invariant under
`promote`/`demote`** (`tilingMapping_{demote,promote}`, `demote_grantsF`,
`promote_grantsF`, and their whole-tiling versions). That is the kickoff §0 theorem.

## The milestones (kickoff §8), as proved

| | Statement | Key theorems |
|---|---|---|
| **M1** | `split` preserves well-formedness (invariant 1). | `WF_split_at` (`Split.lean`) |
| **M2** | Every operation preserves every invariant, **including** the §4 hardware obligations. | below |
| **M3** | The Layer-A representation refines the Layer-S per-`M` mapping (ABI-preservation). | `tilingMapping_demote/promote`, `*_grantsF` |

**M2, by obligation category** (`proof-obligations.md`):

- **TLB coherence (inv7, the §4 crux)** — `unmap_correct`, `mprotect_correct`
  (`Tlb.lean`, `Mprotect.lean`): after the op, no TLB entry caches a stale
  presence/permission; coherence re-established.
- **KAU integrity + dirty/ref aggregation (inv2, inv5)** — `Kau.dirty_of_mem`/`dirty_iff`,
  `Kau.WF.setSlot` (`Kau.lean`): the per-KAU answer is the honest OR over the `c`-vector.
- **Shared object / refcount (inv6), through Rung 3** — `Backing.{add,remove}_wf`,
  `free_iff_unmapped` (`Sharing.lean`); `cowShared_wf`, `cow_conserves`,
  `cow_no_free_while_shared` (`Cow.lean`); `fork_wf`, `forkKernel_breaks_userSafe`
  (`Fork.lean`); and **concrete sharing** — `mappers_length_wf`, the PT-node refcount
  discipline `addRef_wf`/`dropRef_wf`, and the structural errors
  `free_shared_node_strands_siblings`/`orphan_marker_breaks_wf`/`overhang_undercounts`
  (`PtShare.lean`): the cached refcount tracks true sharing, on backing objects *and*
  on shared page-table nodes (which may span object boundaries).
- **Map atomicity (category H)** — `map_atomic`, `goodMap_spec` (`MapAtomic.lean`):
  `map` is all-or-nothing.
- **Superpage promote/demote under heterogeneous tiling (inv3, inv4, inv5)** —
  `promote_dirty_or`, `demote_conservative`, `promote_demote`, `demote_cover`
  (`Tile.lean`); `TilingWF.demote`, `TilingWF.promote` (`Tiling.lean`),
  `WF_merge_at` (`Split.lean`): OR-aggregation, conservative propagation, exact
  split/merge inverse, well-formedness under both directions.
- **fork / COW-share (inv6, category A)** — `fork_wf`, `fork_write_protected`,
  `fork_then_cowbreak_conserves` (`Fork.lean`): forking adds the new sharer and
  write-protects both sides; the full fork→break COW lifecycle conserves the count.
- **swap-out / eviction (categories D, F)** — `swap_roundtrip`, `swapOut_live_wf`,
  `swapOut_preserves_dirty` (`Swap.lean`): the per-`M` save is lossless and drops no
  dirty page; the depopulated KAU stays well-formed.
- **exit / teardown (categories C, D, G)** — `teardown_footprint_zero`,
  `teardown_complete`, `teardown_frees_owned` (`Teardown.lean`): teardown releases the
  whole address space and a solely-owned object's count reaches 0 (reclaimable).
- **fault / populate + the clustering success guarantee (inv2, inv3)** — `populate_wf`,
  `fullUniform_promotable` (`Fault.lean`): a fully and uniformly populated KAU is
  well-formed and *promotable to a `P`-superpage* — the no-external-fragmentation
  guarantee (`clustering-rationale.md`), proved.

## The distinctive part: real bugs are *provable errors*

Each is a failure that actually occurred in telix or pgcl, here proved to be a
*non-theorem* — a definition with the bug fails to satisfy the invariant:

| Theorem | The bug it rules out |
|---|---|
| `unmap_without_flush_breaks_coherence` | unmap that skips the TLB flush → use-after-free (telix #9/#10, pgcl #10) |
| `mprotect_without_flush_breaks_coherence` | write-protect that leaves a stale writable TLB entry (telix #10) |
| `add_wrong_delta_breaks_wf` | mapcount add/remove convention mismatch (pgcl #5) |
| `asymmetric_add_remove_drifts` | migration restore/remove asymmetry → leaked count (pgcl #6) |
| `cowSharedBuggy_breaks_wf` | freeing a still-shared object (telix #8) |
| `buggyMap_violates` / `buggyMap_demo` | partial map reported as success (telix #5/#6) |
| `demoteBuggy_loses_dirty` | demote that drops a dirty bit → lost writeback (pgcl #20) |
| `promoteBuggy_loses_dirty` | promote that peeks one sub-PTE's dirty bit (pgcl #20) |
| (`Frames.lean` `demoteR` frame shift) | fold re-points sub-pages to the wrong physical frame (pgcl #9) |
| `forkBuggy_breaks_wf` | fork that shares a writable page without write-protecting → two writers, one object (telix #10) |
| `forkKernel_breaks_userSafe` | COW-sharing a kernel extent into a child address space (telix #1) |
| `swapOutBuggy_loses_data` / `swapOutBuggy_drops_dirty` | per-KAU (single-slot) swap encoding loses pages / drops a dirty page (pgcl #19) |
| `teardownLeak_strands` | teardown that under-decrements → unreclaimable leak (category G) |
| `gapped_not_promotable` / `divergent_not_uniformPerms` | promoting a partially-populated or divergent-permission KAU (invariant 3) |
| `free_shared_node_strands_siblings` | freeing a shared PT subtree a sibling aspace still references (telix #2) |
| `orphan_marker_breaks_wf` | an orphaned shared-PT marker with no owning group (telix #19) |
| `overhang_undercounts` | per-object refcount under-counts a PT node shared across object boundaries (telix #20) |
| `insert_overlap_breaks` | inserting an overlapping extent into the B+-tree (ordered map) corrupts the ordering invariant (telix #14 / pgcl #14) |

The catalogs `failure-modes-{telix,pgcl}.md` map the full bug history to the invariants.

## The trust line (kickoff §5), drawn explicitly

- **Proved (sequential):** Layers S and A; the refinement S ⟸ A; invariants 1–7 and
  the Property-1 coherence obligations; the COW/promotion preconditions made explicit
  (`PromotableF` for physical contiguity; the heterogeneous-tiling regime for
  intra-KAU sizes).
- **Trusted, not proved:** the hardware behaves as the abstract translation model says
  (the MMU/TLB, invalidation instructions). On **software-refill** architectures this
  trust shrinks to a provable refill handler — see `mmu-variants.md`.
- **Separate track, done:** Property 2 (concurrent TLB-shootdown ordering under relaxed
  memory) — the standalone Coq + Iris / litmus development (`../property2/`): the litmus
  necessity family on the Arm VMSA model, and the Iris protocol proofs under both
  sequential consistency and weak memory (iRC11/gpfsl).
- **In progress:** Layer I (refinement to the real implementation) — first rung done
  (`ExtentMap.lean`, the telix B+-tree's ordered-map semantics refined to Layer A);
  the balanced tree-node structure, PTE bit-encodings, and literal-Rust validation
  (e.g. Aeneas) remain. Not required for the above to be a complete, honest result on
  its own terms (as the brief's §5 states of seL4's own lines).

## Module index (`../proof/Tessera/`)

`Basic` (extents, WF) · `Split` (M1 `split`/merge) · `Tlb` (unmap coherence) ·
`Mprotect` (mprotect coherence) · `Kau` (PTE-vector) · `Sharing` (refcount) ·
`Cow` (COW-break) · `Fork` (fork/COW-share) · `PtShare` (Rung-3 concrete sharing, PT-node refcounts) ·
`MapAtomic` (map atomicity) ·
`Swap` (swap-out) · `Teardown` (exit/teardown) · `Fault` (fault/populate, promote-on-fill) ·
`Tile` (promote/demote coarsening) · `Tiling` (heterogeneous tiling WF) ·
`Refinement` (superpaging invisible) · `RefinementS` (Layer-S mapping) ·
`Frames` (physical frames) · `ExtentMap` (Layer-I: ordered extent map = telix B+-tree, refined to Layer A).

## Why it is grounded

The Layer-A model is idealized (kickoff §2); telix's physical `ExtentEntry` B+-tree and
pgcl's `struct page` are Layer I (deferred). But every theorem targets a *real* failure
mode mined from the two implementations' histories, and the design rationale
(`clustering-rationale.md`), architecture spectrum (`mmu-variants.md`), and intra-KAU
tiling decision (`intra-kau-tiling.md`) are recorded. The result is the brief's stated
goal: *a coherent sequential proof of Layers S/A with the Property-1 coherence
obligations — a complete and honest result in itself.*

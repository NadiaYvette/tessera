# Tessera — formalization status & decisions

A living map from the brief (`tessera-verification-kickoff.md`) to the actual proof
artifacts in `../proof/`, plus the modeling decisions and rationale a future session
needs. Build/verify instructions live in [`../proof/README.md`](../proof/README.md).

## Prover & toolchain

- **Lean 4, `leanprover/lean4:v4.16.0`, core-only** for the sequential layer
  (M1–M3). Rationale per brief §7; details in `../proof/README.md`. `Nat`,
  `List.Pairwise`, and `omega` have sufficed so far with no mathlib dependency.
- **Eventual Coq + Iris track** for the hardware-state / concurrency layer (Property
  2 — TLB-shootdown soundness under relaxed memory, and the relaxed-virtual-memory
  models that treat the TLB and page-table walk as first-class). The brief (§7)
  routes this to Coq because Iris, the weak-memory Iris extensions, and the
  relaxed-VM lineage live there to a maturity found nowhere else. Coq 8.20.1 + opam
  are already installed; `coq-iris` and the herd/litmus toolchain would be added when
  that track opens. **This is anticipated and on the roadmap, not yet needed.**
- **Toolchain latitude (standing).** Building or modifying our own
  toolchains/languages/compilers/libraries is a ready option for this project — more
  so than typical. Concretely this means: pulling/patching mathlib, building a custom
  Lean or Coq, adding custom tactics, or installing/patching Iris are all on the
  table when they earn their weight. The bias remains *core-only and self-contained
  until a need is concrete*, but the ceiling is high.

## Layers (brief §2)

| Layer | What | Where | Status |
|-------|------|-------|--------|
| **S** — Specification | abstract mapping VA→(PA,perm); the ABI promise | presence (`Tlb.lean`); permissions `tilingMapping` (`RefinementS.lean`); **(frame,perm)** `Tile.grantsF` (`Frames.lean`) | ✅ the full per-granule (physical frame, permission) mapping is well-defined and shown invariant under the representation (M3) |
| **A** — Algorithm | extents as pure data; ops as pure functions; the central theorems | `Basic.lean`, `Split.lean`, `Tlb.lean` | M1 done; M2 flagship (unmap/TLB) done; rest in progress |
| **I** — Implementation | concrete B+-tree / PTE bit-encodings / refcounted sharing groups | **`ExtentMap.lean`** (ordered extent map = telix `mm/extent.rs` B+-tree semantics) | 🔶 **first rung done**: the ordered-map invariant **refines** Layer-A `WF` (`WFI_imp_WF`, axiom-free); `lookup` sound+complete vs the induced mapping; `insert` refines the set-add and preserves the order, while an overlapping insert is a provable error (telix #14). PTE bit-encodings, refcounted groups, and the balanced tree-node structure remain |

## Invariants (brief §3) → formal status

| # | Invariant | Lean | Status |
|---|-----------|------|--------|
| 1 | Disjoint, aligned, power-of-two extents | `Extent.Valid`, `Disjoint`, `WF` (`Basic.lean`) | ✅ defined; **preserved by `split`** (`WF_split_at`) |
| 2 | KAU integrity (c PTE-vector slots, P-aligned) | `Kau.WF` (`Kau.lean`) | 🔶 defined (Rung 1); preserved by slot update (`WF.setSlot`); global mapcount discipline (Rung 2) done in `Sharing.lean` |
| 3 | Superpage uniformity (promote precondition) | `Tile.Promotable` + `promote_uniform` (`Tile.lean`) | 🔶 promote precondition (adjacent, equal-size, uniform-perms) defined; the promoted tile is uniform |
| 4 | Consistent split/merge | `WF_split_at` + `WF_merge_at` (`Split.lean`), `TilingWF.demote` + `TilingWF.promote` (`Tiling.lean`), `promote_demote` (`Tile.lean`) | ✅ **both split and merge** preserve WF; a heterogeneous tiling stays well-formed under **both** demote and promote (each reusing M1); promote is demote's exact inverse |
| 5 | Dirty/referenced aggregation (OR over vector) | `Kau.dirty` (`Kau.lean`); `Tile` coarsening (`Tile.lean`) | ✅ honest per-`M` OR (`Kau.lean`); and under heterogeneous tiling: promote OR-aggregates, demote conservatively propagates, both preserve the per-KAU dirty-OR — peeking/dropping a coarse bit is a provable error |
| 6 | COW consistency (refcounts reflect sharing) | `Backing` (`Sharing.lean`, `Cow.lean`, `Fork.lean`, `PtShare.lean`) | ✅ refcount discipline (Rung 2) + **COW-break** (`Cow.lean`, telix #8) + **fork/COW-share** (`Fork.lean`, telix #1/#10) + **Rung 3 concrete sharing** (`PtShare.lean`): concrete `(aspace, vaddr)` sites, the COW-group mapper set, and **shared PT-node refcounts** — freeing a node a sibling still references (telix #2), an orphaned shared marker (telix #19), and the per-object boundary overhang (telix #20) are each provable errors |
| 7 | TLB coherence (`TLB ⊆ mapping`) | `TlbCoherent` (`Tlb.lean`), `PTlbCoherent` (`Mprotect.lean`) | ✅ presence form preserved by `unmap`, and permission form (exact perm-agreement, which subsumes presence) by `mprotect`; a flush-less `unmap`/`mprotect` provably violates it |
| 8 | Cache coherence (VIVT/VIPT) | — | out of initial scope (brief §3); no catalogued bug yet exercises it |

## Hardware obligations (brief §4)

- **Property 1 (sequential coherence obligation) — IN SCOPE.** `Tlb.lean`:
  `unmap_correct` proves `unmap r` leaves `r` unmapped, leaves no TLB entry covering
  `r`, and preserves `TlbCoherent`; `unmap_without_flush_breaks_coherence` proves the
  flush-less variant violates coherence — the §4 "missing flush is a provable error,"
  realized. Extending to `mprotect`/`demote` (perm-agreement coherence, not just
  presence) is the next M2 step.
- **Property 2 (concurrent observation) — DEFERRED.** Isolated litmus/herd + Coq/Iris
  track (above). The bug catalogs confirm this is the right line to draw (see
  `failure-modes.md` §"Scope validation").

## Hardware model & MMU variants (brief §5 trust line)

The brief's "the MMU walks page tables thus" is *trusted* — but only on
**hardware-page-table-walker** architectures (x86-64, ARM64, RISC-V). On
**software-refill TLB** architectures (MIPS, SPARC; a telix target) there is no
hardware walker: the refill handler is *our code*, so its correctness becomes a
**theorem, not an assumption** — the trust line moves down and the result is stronger.
**Inverted/hashed** page tables (PowerPC pre-Radix, PA-RISC) change the Layer-I target
but not the invariants. Consequences for the development: Layer A and the TLB model
(`Tlb.lean`, TLB-as-explicit-set) are kept **MMU-agnostic** (the TLB-as-cache framing
is literally the software-refill model); Layer I is **parameterized over the MMU
model**; and on software-refill targets a refill-handler-correctness theorem is added.
Full treatment: `mmu-variants.md`.

## Safety vs. liveness — the clustering rationale (brief §6)

The clustering layer does two jobs for superpaging — (1) *guaranteed small superpages*
(the KAU is the allocation grain, so a full uniform KAU always promotes to a
`P`-superpage with no external fragmentation) and (2) *bridging `M` to the first big
superpage* (absorb most of the `S/M` ratio into `c`, leaving a small assembly ratio
`S/P`; e.g. `512 = 64 × 8` with a 256 KiB KAU). Both are **liveness / performance**
properties, complementary to the safety invariants this development proves. They touch
the model in three ways: KAU contiguity becomes part of **inv2** (the `c` slots are
`c` contiguous `P`-aligned `M`-pages); **`promote` (category E) splits into two
regimes** — *intra-KAU* (always satisfiable once the KAU is full + uniform) and
*inter-KAU assembly* (fragmentation-dependent); and an optional Layer-A success lemma
— *"a full uniform KAU meets the `P`-superpage promotion precondition"* — formalizes
use 1. Full treatment: `clustering-rationale.md`.

## Milestones (brief §8)

- **M1 — `split` preserves well-formedness.** ✅ Complete, axiom-clean
  (`propext`, `Quot.sound`). `Split.lean`.
- **M2 — all ops preserve all invariants incl. coherence.** ✅ **The operation matrix
  (`proof-obligations.md` Part 2) is complete: every operation has a module.** Flagship
  done: TLB explicit, `unmap` coherence proven, missing-flush-is-an-error proven
  (`Tlb.lean`). Remaining, prioritized by the threat model (`failure-modes.md`):
  (a) the PTE-vector + per-KAU aggregation (inv2, inv5) — **Rung 1 done** (`Kau.lean`:
  vector structure, honest dirty/ref OR, inv2 preserved by slot update) and **Rung 2
  done** (`Sharing.lean`: the global mapcount add/remove discipline — under/over-count
  is a provable error, free-while-mapped & leak impossible); (b) **`map` all-or-nothing atomicity done** (`MapAtomic.lean`: a partial map reported
  as success is a provable contract violation — telix #5/#6); (c) COW-break
  consistency — **done** (`Cow.lean`: the break preserves the refcount discipline,
  conserves the writer's mapping, keeps a still-shared object unreclaimable — telix
  #8; reclaiming a shared object is a provable error); the concrete sharing-group +
  PTE-vector structure is deferred. (d) promote/demote/merge —
  **coarsening core done** (`Tile.lean`, under the chosen **heterogeneous** tiling:
  promote OR-aggregates dirty/ref, demote conservatively propagates, both preserve the
  per-KAU dirty-OR; promote is demote's exact inverse; promote precondition inv3;
  dropping/peeking a coarse bit is a provable error), and the **structural tiling
  well-formedness** is established (`Tiling.lean`: `TilingWF` + `demote` preserves it,
  reusing M1); merge-WF and the refinement to the per-`M` vector remain.
  (e) **mprotect perm-agreement TLB coherence done** (`Mprotect.lean`:
  exact-perm coherence subsuming presence; a flush-less `mprotect` is a provable
  error — the stale-write-permission bug, telix #9/#10). Category A complete for the
  in-scope operations.
  **(f) the remaining operations of the matrix — done**, so every row of
  `proof-obligations.md` Part 2 now has a module:
  • **fork / COW-share** (`Fork.lean`): the entry to COW (Cow.lean is the exit) — the
  refcount bump for the new sharer, the *write-protect* of both sides (omitting it is a
  provable error — two writers to one object, telix #10), the kernel-extent exclusion
  (sharing a kernel object into a child is a provable error, telix #1), and the
  fork→break lifecycle conservation.
  • **swap-out / eviction** (`Swap.lean`): lossless per-`M` save + depopulate; the
  per-KAU (single-slot) encoding loses data and drops dirty pages — provable errors
  (pgcl #19).
  • **exit / teardown** (`Teardown.lean`): complete release of an address space
  (footprint → 0, every granule freed) and the refcount side (a solely-owned object
  frees; an under-decrementing teardown strands an unreclaimable leak — provable error).
  • **fault / populate** (`Fault.lean`): the inverse of `unmap`, with the **clustering
  success guarantee** — a fully and uniformly populated KAU is well-formed and
  *promotable* to a `P`-superpage (invariant 3, no external fragmentation); a gapped or
  divergent-perm KAU is provably *not* promotable.
  All four axiom-clean (`propext`, `Quot.sound`).
  **(g) Rung 3 — concrete sharing, done** (`PtShare.lean`): sites become concrete
  `(aspace, vaddr)`; the COW-group mapper set is `mappers`; and **shared PT nodes carry
  their own refcount** (`PtNode`) — the structural layer Rung 2's abstract sites could
  not reach. Freeing a node a sibling still references (telix #2), an orphaned shared
  marker (telix #19), and the per-object **boundary overhang** that under-counts a node
  shared across objects (telix #20) are each provable errors. *Still open (deferred, not
  matrix gaps):* the full radix/PT-subtree structure and the tiling↔per-`M`-vector
  refinement.
- **M3 — refinement S ⟸ A (ABI-preservation).** ✅ **Done at the tiling level**
  (`Refinement.lean` + `RefinementS.lean`). The ABI-visible view is `Tile.grants`; the
  induced Layer-S partial function is `tilingMapping : Nat → Option Perm`. Proved:
  (i) **functionality** (`TilingGrants_functional`) — under well-formedness the grants
  relation is single-valued, so the Layer-S object is a genuine *function* (this is
  where invariant-1 disjointness earns its keep); (ii) **agreement**
  (`tilingMapping_eq_some_iff`) — the induced mapping *is* the grants relation; (iii)
  the **refinement** (`tilingMapping_demote`/`tilingMapping_promote`) — that Layer-S
  mapping is **invariant under promote/demote**: the representation may be re-tiled
  any way (one superpage, individual `M`-entries, any heterogeneous mix) and the ABI's
  mapping does not move. Kickoff §0's top-level theorem, proved at the tiling layer.
  **Physical frames done** (`Frames.lean`): Layer S extended to the full VA → (physical
  frame, permissions) — `Tile.grantsF` with the linear translation `frame + (v-base)`,
  invariant under demote/promote (`demote_grantsF`/`promote_grantsF` and their tiling
  versions). `demoteR` shifts its frame so the per-granule physical address is
  preserved — pgcl #9 (fold reads wrong sub-page) is now a *non-theorem*; and
  `PromotableF` surfaces the real **physical-contiguity** precondition for promotion.
  *Remaining to extend further (optional):* relate the mapping to the `Basic.lean`
  extent set (largely subsumed by `Tile.toExtent`).
- **M4 — Layer-I refinement (the real implementation).** 🔶 **Four Lean rungs**
  (`ExtentMap`, `BTree`, `Pte`, `RadixPt`, all axiom-clean) **+ literal executable Rust**
  (`rust/extent-kani/`, Kani-verified).
  (`ExtentMap.lean`): the **ordered extent map** — the semantic model of telix's
  `mm/extent.rs` B+-tree (an ordered, non-overlapping map keyed by base). Proved: its
  ordering invariant **refines** Layer-A `WF` (`WFI_imp_WF`, axiom-free); `lookup` is
  sound and complete against the induced mapping; `insert` refines the set-add
  (`insert_mem`) and **preserves** the ordering invariant when the new extent is disjoint
  (`insert_ordered`), while an overlapping insert provably breaks it
  (`insert_overlap_breaks` = telix #14 / pgcl #14). This connects the verified algorithm
  to telix's actual data structure.
  **Further rungs done:** **`BTree.lean`** — the tree-node structure (an ordered search
  tree whose in-order traversal *is* the `ExtentMap` ordered map: `bst_ordered` +
  `lookup_sound`, giving tree ⟶ ordered map ⟶ Layer A); **`Pte.lean`** — the PTE
  bit-encoding leaf (`encode`/`decode` round-trips on valid/perm/frame, so the descriptor
  word realizes the Layer-A `(valid, perm, frame)` leaf; a field-overlapping layout
  provably corrupts the translation, `encodeBuggy_corrupts`); **`RadixPt.lean`** — the
  refcounted PT *subtree* (a shared subtree carries its mappings; freeing it while a
  sibling references it is a provable UAF, `free_shared_subtree_uaf` = telix #2; the
  discipline composes up the tree).
  **Literal Rust reached** (`rust/extent-kani/`): telix's real `extent.rs` is a
  raw-pointer B+-tree (17 `unsafe`, `*mut u8` nodes) — outside Aeneas's safe-Rust model,
  so the right tool is **Kani** (bounded model-checking via CBMC). A faithful heap-free
  Rust `insert3` (the bounded instance of `ExtentMap.insert`) is **Kani-verified** to
  preserve the ordering invariant for any disjoint insert, overflow-free (157 checks,
  `VERIFICATION: SUCCESSFUL`) — the literal-Rust counterpart of `insert_ordered`, the
  first time the development touches executable Rust, not a model. *Remaining:* the
  multi-level B+-tree balancing (insert-with-split, performance-only); wiring the Kani
  harness against telix's *deployed* module (needs kernel-dep stubs); a *full* (not
  bounded) proof of the unsafe code would use Verus.

## Formalization decisions (and why)

1. **Units = M (granules).** All `base`/`size`/`vbase` are granule counts. Layer-A
   invariants are scale-invariant; M's byte size belongs at S/I. Keeps arithmetic
   about powers of two, where `omega` is strong.
2. **`split` = buddy halving.** Size `2^(k+1)` → two `2^k` halves. The canonical,
   alignment-preserving, tiling split; everything else (n-way, arbitrary boundary)
   composes from it.
3. **Abstract mapping as a predicate** (`Nat → Prop`) and **TLB as a `List
   TlbEntry`**, kept as *separate* state (brief §3). This isolates the §4 coherence
   obligation cleanly and matches the brief's separation of the abstract mapping
   (the refinement object) from the representation.
4. **Presence-coherence first.** `TlbCoherent` currently means "no cached entry for
   an unmapped granule" — exactly the unmap UAF. Translation/perm-agreement (for
   mprotect, and inv8) is the deliberate next increment.
5. **`TlbEntry.Overlaps` is an `abbrev`** so its `Decidable` instance (an `And` of
   `Nat` comparisons) is found automatically and can drive the flush filter.
6. **Core-only, axiom-clean.** Every result is checked to depend only on Lean's
   standard sound axioms (`#print axioms`), never `sorryAx`.

## Where the real systems sit relative to the model

The Layer-A extent is idealized (brief §2); telix's physical `ExtentEntry` B+-tree,
per-VMA lazy promotion, and implicit (walked) PTE vectors are **Layer I**. telix is
the design reference; pgcl is the failure-mode evidence. See `failure-modes.md` for
the telix-vs-pgcl roles and `../proof/README.md` for the telix correspondence notes.

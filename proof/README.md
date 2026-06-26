# Tessera — proof development

Formal verification of a **clustered virtual-memory manager with superpages**: a
VMM whose kernel allocation unit is a power-of-two multiple of the hardware's
minimum mapping granularity, with translation state tracked at the finer
granularity so the clustering is invisible to the ABI.

The verification brief — the authoritative statement of model, invariants,
hardware obligations, trust boundary, and milestones — is
[`../doc/tessera-verification-kickoff.md`](../doc/tessera-verification-kickoff.md).
Read it first. The companion docs hub is
[`../doc/formalization-status.md`](../doc/formalization-status.md) (invariant- and
milestone-by-milestone status + decisions) and
[`../doc/failure-modes.md`](../doc/failure-modes.md) (the empirical threat model
mined from telix/pgcl). For a one-page statement of *what is proved*, see
[`../doc/RESULTS.md`](../doc/RESULTS.md).

## Status

| Milestone | Statement | State |
|-----------|-----------|-------|
| **M1** | Define the extent and well-formedness (invariants 1–2); define `split`; prove `split` preserves well-formedness. | ✅ **complete, axiom-clean** |
| **M2** | All operations (map, unmap, merge, promote, demote, COW-break) preserve all invariants, **including** re-establishing TLB/cache coherence — so an `unmap` without its flush fails to verify. | 🔶 **flagship done** — TLB modeled as explicit state; `unmap` proven to re-establish coherence (`Tlb.lean`, `unmap_correct`) and a flush-less `unmap` proven to violate it (`unmap_without_flush_breaks_coherence`). PTE-vector aggregation **Rung 1 done** (`Kau.lean`: inv2 + honest inv5 dirty/ref OR, so the pgcl-#20 peek-slot-0 bug is unrepresentable); shared-object mapcount **Rung 2 done** (`Sharing.lean`: global add/remove count discipline — under/over-count is a provable error, free-while-mapped & leak impossible); map-atomicity (`MapAtomic.lean`, a partial map reported as success is a provable error) and mprotect perm-agreement TLB coherence (`Mprotect.lean`, a flush-less mprotect a provable error) **done**, plus promote/demote coarsening under heterogeneous tiling (`Tile.lean`: promote OR-aggregates, demote conservatively propagates, peeking/dropping a dirty bit a provable error). COW-break consistency (`Cow.lean`, telix-#8 no-free-while-shared) and heterogeneous tiling well-formedness (`Tiling.lean`) **done**. Remaining: merge-WF, the tiling↔per-`M`-vector refinement, and M3 (ABI-preservation). |
| **M3** | Refinement: the Layer-A extent/superpage representation refines the Layer-S per-`M` mapping (ABI-preservation). | ✅ **done (tiling level)** — the induced Layer-S mapping `tilingMapping` is well-defined (functional under WF, `TilingGrants_functional`), equals the grants relation (`tilingMapping_eq_some_iff`), and is **invariant under promote/demote** (`tilingMapping_{demote,promote}`): the ABI cannot tell a superpage from individual entries from a partial population (`RefinementS.lean`). Extending `tilingMapping` to the `Basic.lean` extent set + physical frames pending. |

M1's theorems (`Tessera.WF_split_at`, `WF_split_cons`, and the `split_*` lemmas)
depend only on `propext` and `Quot.sound` — Lean's standard sound axioms — with no
`sorryAx`. Verify with the axiom check below.

## Prover

**Lean 4, toolchain `leanprover/lean4:v4.16.0`** (pinned in `lean-toolchain`),
**core only — no mathlib dependency.**

Rationale (brief §7): the sequential milestones M1–M3 need only ordinary
higher-order logic with good inductive-type support; the brief names Lean 4 and
Isabelle/HOL as the two strong choices, reserving Coq for *if* the concurrent
Property 2 (TLB-shootdown soundness under weak memory) becomes a committed goal —
which it is not. Of the provers installed in this environment (Lean 4.16.0, Coq
8.20.1, Agda 2.8.0), only Lean is one of the two recommended, and its
inductive/arithmetic automation (`omega`, structural induction) is exactly what
M1 needs. Core-only keeps the artifact fast to check, self-contained, and easy to
hand off (a value the brief stresses in §1); `Nat`, `List.Pairwise`, and `omega`
suffice. mathlib remains an additive option should M2/M3 want `Finset` /
partial-function machinery.

## Layout

```
proof/
  lean-toolchain        leanprover/lean4:v4.16.0
  lakefile.toml         core-only library `Tessera`
  Tessera.lean          root: re-exports the development
  Tessera/
    Basic.lean          Layer-A model: Perm, Extent, IsPow2, Valid, Disjoint, WF
    Split.lean          split (buddy halving) + the M1 theorem
    Tlb.lean            M2 flagship: TLB as explicit state; unmap coherence (§4)
    Kau.lean            M2 Rung 1: the c-slot PTE-vector; inv2 + inv5 (honest dirty/ref OR)
    Sharing.lean        M2 Rung 2: shared backing object; mapcount add/remove discipline (inv6)
    MapAtomic.lean      M2 category H: map all-or-nothing; partial-map-as-success a provable error
    Mprotect.lean       M2 category A: mprotect perm-agreement TLB coherence; flush-less mprotect a provable error
    Tile.lean           M2 category E: promote/demote under heterogeneous tiling; dirty/ref coarsening (inv3/4/5)
    Tiling.lean         M2 category E: heterogeneous tiling well-formedness; demote preserves it (reuses M1)
    Cow.lean            M2: COW-break consistency (inv6); no-free-while-shared (telix #8)
    Refinement.lean     M3 seed: superpaging invisible — per-granule perms invariant under promote/demote
    RefinementS.lean    M3 full: Layer-S mapping well-defined (functional) + invariant under promote/demote
    Frames.lean         M3 + physical frames: Layer S = VA→(frame,perm); pgcl-#9 a non-theorem; contiguity precond
```

## Build & verify

```sh
cd proof
lake build                       # checks every proof
# axiom hygiene (should print only [propext, Quot.sound]):
echo 'import Tessera
#print axioms Tessera.WF_split_at' > /tmp/Check.lean
lake env lean /tmp/Check.lean
```

## The model in one screen (Layer A)

- **Units are `M`** (the minimum mapping granularity). All `base`/`size` are
  granule counts. Layer-A invariants (alignment, power-of-two sizing,
  disjointness, tiling) are scale-invariant; `M`'s byte size enters only at
  Layer S / Layer I. The cluster factor `c` (so `P = c·M`) and KAU-integrity
  (invariant 2) arrive with the superpage operations in M2.
- **`Extent = (base, size, perms)`** — an aligned, power-of-two-sized run of
  granules with uniform permissions.
- **`Extent.Valid e := IsPow2 e.size ∧ e.size ∣ e.base`** — invariant 1.
- **`Disjoint a b := a.hi ≤ b.lo ∨ b.hi ≤ a.lo`** over half-open intervals
  `[lo, hi)`; symmetric.
- **`WF es := (∀ e ∈ es, e.Valid) ∧ es.Pairwise Disjoint`** — a well-formed
  extent set models the mapped part of an address space.
- **`split`** = buddy halving: an extent of size `2^(k+1)` into two adjacent
  halves of size `2^k` (`splitL`, `splitR`) that tile it.
- **`WF_split_at : WF (pre ++ e :: post) → e.Splittable → WF (pre ++ e.split ++ post)`**
  — the M1 theorem, general over which extent is split.
- **TLB (M2 flagship, `Tlb.lean`):** abstract mapping `Mapping := Nat → Prop` and
  TLB `List TlbEntry` as separate state; `TlbCoherent m tlb` is invariant 7
  (`TLB ⊆ mapping`). `unmap_correct` proves `unmap r` leaves `r` unmapped, leaves no
  TLB entry covering `r`, and preserves coherence; `unmap_without_flush_breaks_coherence`
  proves the flush-less `unmap` violates it — §4's "missing flush is a provable error."

## Correspondence to the real systems (telix / pgcl)

The Layer-A extent here is **deliberately idealized** (brief §2): an aligned
power-of-two run, with operations as pure functions. The concrete B+-tree of
physical `ExtentEntry`s in `telix/kernel/src/mm/extent.rs`, the per-VMA superpage
eligibility checks, and the lazy promotion in `fault.rs` belong to **Layer I**
(deferred). Notable points to honor when Layer I is reached, and constraints to
fold into M2's model:

- telix: `MMUPAGE_SIZE (M) = 4096`; `PAGE_SIZE (P = c·M)` is a power-of-two,
  compile-/boot-time selectable (16K/64K/128K/256K); `PAGE_MMUCOUNT = c`
  (`kernel/src/mm/page.rs`). The smallest superpage level is currently 2 MiB on
  all arches.
- telix tracks extents in **physical** space (page cache), separate from per-VMA
  **virtual** mapping state; the "vector of `c` PTEs per KAU" is *implicit*
  (walked from the page table), not a stored array. Superpage promotion checks
  presence + uniform permissions + physical contiguity + no COW sharing
  (`fault.rs`), and demotion issues `tlbi … ; dsb ish; isb` (e.g.
  `arch/aarch64/mm.rs`) — direct evidence that §4's TLB-coherence obligation is a
  live concern in the code, which M2 must capture.
- COW is reservation-aware (epoch/shared-mask bitmaps, N-way fork); the brief's
  "COW write demotes the whole extent" is a Layer-A simplification to encode as
  an explicit precondition (brief §3), not telix's exact mechanism.

These are recorded so a future session does not mistake the idealized Layer-A
model for unfaithfulness, and knows where the abstraction will be discharged.

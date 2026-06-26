# Working outward from `unmap`: the proof-obligation map

## Method

`unmap` is not a checkbox "flagship." It is the **worked seed**: one operation
that, fully specified, touches almost every obligation the VMM must discharge.
The method this doc records:

1. Decompose `unmap r` into the **categories** of obligation it reveals (Part 1).
2. For each category, enumerate **every** operation and situation that must
   discharge it — the union is "everything needing to be proved" (Part 2).
3. Read off the prioritized M2/M3 work-list (Part 3).

Cross-references: invariants and milestones in `tessera-verification-kickoff.md`;
bug evidence in `failure-modes.md`; formal status in `formalization-status.md`.

## Part 1 — `unmap r` decomposed into obligation categories

| | Category (what `unmap` must do) | Invariant | Catalog evidence | Status |
|---|---|---|---|---|
| **A** | **Invalidate the TLB** for `r` — no cached translation survives for a now-unmapped granule. Stride must be `M`, i.e. cover all `c` sub-entries / the whole superpage entry. | inv7 / Property 1 | telix #9,#10; pgcl #10,#12 | ✅ proven (`Tlb.lean`) |
| **B** | **Maintain caches** for `r`'s virtual addresses (VIVT/VIPT): a later mapping of the same VA must not read stale lines. Same coverage concern as A. | inv8 | (none yet exercised) | out of initial scope |
| **C** | **Edit the representation so the induced mapping loses exactly `r`.** If `r` is interior to an extent, that extent must **split**; alignment/disjointness preserved; post-state representation induces post-state mapping. | inv1, inv4, refinement | pgcl #14 (overlap), telix #8 | partial: M1 proves `split` keeps WF; the refinement is M3 |
| **D** | **Leave the KAU faithfully partially-populated** — gaps in the `c`-vector are a legal state. | inv2 | pgcl #3,#19 (gapped KAU) | pending (M2) |
| **E** | **Demote first if `r` cuts a superpage** — one entry maps all `c` uniformly, so a partial unmap is illegal until the superpage is demoted to a vector. | inv3 | telix #9; pgcl #9 | pending (M2) |
| **F** | **Honor aggregated dirty/referenced** — write back a dirty file KAU before dropping it; dirty = OR over the `c` sub-PTEs (peeking slot 0 loses writes). | inv5 | pgcl #20 | pending (M2) |
| **G** | **Reclaim or refcount** — freeing the *last* mapping frees the backing object + empty PT nodes; unmapping a *shared* mapping **decrements, does not free**; the count changes by the true delta. | inv6 (the shared object) | telix #2,#8,#20; pgcl #1,#5 | pending (M2) |
| **H** | **Be all-or-nothing** — complete or roll back; never a half-edited representation (the dual of map-atomicity). | Property-1-style postcondition | telix #5,#6 | pending (M2) |
| **(I)** | **Tolerate concurrency** — race vs. a fault/teardown on another core; shootdown IPI ordering for remote observation. | Property 2 | telix #3,#10(remote),#17 | deferred (Coq+Iris/litmus) |

So a *single* operation, taken seriously, radiates into all eight invariants plus
both hardware properties. That is the point: the categories above, not `unmap`
itself, are the starting points.

## Part 2 — the operation × obligation matrix

Each category A–H is an obligation that recurs across many operations. The matrix
is the coverage to prove. `✓` = must discharge; `~` = conditional; `–` = n/a.
(Property 2 / category I is deferred for every row.)

| Operation | A TLB | B cache | C repr/split | D vector | E superpg | F dirty/ref | G refcount | H atomic |
|---|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| fault / populate | – | – | ✓ | ✓ | ~ promote | – | ✓ | ✓ |
| map | – | – | ✓ | ✓ | – | – | ✓ | ✓ |
| **unmap** (seed) | ✓ | ~ | ✓ | ✓ | ~ demote | ✓ | ✓ | ✓ |
| mprotect | ✓ | ~ | ✓ | ✓ | ~ demote | – | – | ✓ |
| promote | ~ | – | ✓ | ✓ | ✓ (precond) | ✓ aggregate | – | ✓ |
| demote | ✓ | ~ | ✓ | ✓ | ✓ | ✓ distribute | – | ✓ |
| split | – | – | ✓ | ✓ | – | – | – | ✓ |
| merge | – | – | ✓ | ✓ | ~ re-promote | ✓ aggregate | ~ | ✓ |
| fork / COW-share | ✓ wprot | ~ | ✓ | – | – | – | ✓ | ✓ |
| COW-break | ✓ | ~ | ✓ | ✓ | ~ demote | – | ✓ | ✓ |
| swap-out | ✓ | ~ | ✓ | ✓ | – | ✓ writeback | ✓ | ✓ |
| exit / teardown | ✓ | ~ | ✓ | ✓ | – | ✓ | ✓ | ~ |

Key obligation + evidence per operation:

- **fault/populate** — install one/more sub-PTEs; if the KAU becomes complete and
  uniform, *may* promote (E). Atomic install (H). Bumps the object's count (G).
- **map** — establish an extent; **all-or-nothing** (H) is telix's #1 bug class
  (#5,#6: ignored result → partial mapping). New mapping bumps refcount (G).
- **unmap** — the seed; see Part 1.
- **mprotect** — narrowing perms must flush (A: telix #9); split at boundaries (C);
  demote if perms diverge across a superpage (E). Perm-*agreement* TLB coherence
  (richer than presence) — the next increment past the proven unmap result.
- **promote** — precondition is inv3 (all `c` present + uniform); aggregate dirty/ref
  into the superpage entry (F). Replacing `c` entries by one same-translation entry
  is presence-coherent, so A is conditional (hardware may still require it).
- **demote** — must flush the cached superpage entry (A: telix #9, pgcl #9), else a
  stale superpage translation persists; distribute the aggregate bits back to the
  `c` sub-PTEs (F).
- **split / merge** — inv4. split proven (M1); merge is the dual and may re-promote
  (E) and must aggregate the merged dirty/ref (F) and reconcile sharing (G).
- **fork / COW-share** — bump refcount + mark shared (G: the shared object); must
  **write-protect existing writable mappings and flush** (A: telix #10); must **not**
  share kernel extents (telix #1 — inv2+inv6).
- **COW-break** — decrement the shared object, install a private copy (G); a write to
  a superpage-mapped shared extent **demotes the whole extent first** (E — the
  brief's §3 precondition to make explicit); flush (A); atomic copy (H).
- **swap-out** — depopulate slots (D, partial), write back aggregated dirty (F),
  flush (A), encode the swap slot per-`M` (G: pgcl #19).
- **exit/teardown** — unmap-all + free everything (A,C,D,G); the teardown-vs-live-walk
  race is Property 2 (telix #3,#17).

## Part 3 — the M2 work-list this implies

Ordered by threat-model weight (`failure-modes.md`) and dependency:

1. **Category A for the rest** — `mprotect`/`demote` perm-agreement TLB coherence
   (extend the proven presence-coherence to translation/perm content). [unblocks E]
2. **Category G — the shared backing object & refcount discipline** — the central
   novelty (pgcl #1,#5); see the abstraction ladder below for *at what level*.
3. **Categories D + F — the PTE-vector, partial population, dirty/ref aggregation**
   (inv2, inv5; pgcl #20). Local, cheap, prerequisite for E/promote.
4. **Category E — promote/demote** with the inv3 precondition (and the forced demote
   that A/C/D/H above keep referring to).
5. **Category C — split/merge complete** (merge is the remaining half of inv4) and
   **map/unmap atomicity (H)** as all-or-nothing postconditions (telix #5,#6).
6. **Category G — COW-share/COW-break** with the explicit superpage-COW precondition
   (inv6; telix #1,#7,#8,#19,#20).

Then **M3** ties Layer A to Layer S (refinement), discharging category C's
refinement obligation and forbidding the wrong-sub-page reads (pgcl #9).

## Status — the matrix is covered ✅

Every operation in the Part 2 matrix now has a Lean module discharging its
obligations (all axiom-clean):

| Operation | Module | Operation | Module |
|---|---|---|---|
| fault / populate | `Fault.lean` | split / merge | `Split.lean`, `Tiling.lean` |
| map | `MapAtomic.lean` | fork / COW-share | `Fork.lean` |
| unmap (seed) | `Tlb.lean` | COW-break | `Cow.lean` |
| mprotect | `Mprotect.lean` | swap-out | `Swap.lean` |
| promote / demote | `Tile.lean`, `Tiling.lean` | exit / teardown | `Teardown.lean` |

So the Part-1 categories A–H are each discharged across the operations that touch
them, and `unmap`'s "radiation into all eight invariants" is realized as a covered
grid. Property 2 (category I) is the separate concurrent track (`../property2/`).
*Deferred (not matrix gaps):* Rung-3 concrete sharing-group structure (telix #20
boundary overhang), and the tiling↔per-`M`-vector refinement.

## Appendix — the abstraction ladder for the "shared backing object"

This is the clarification of "model the shared object explicitly vs keep it
abstract." There is not one alternative but a **ladder**; each rung catches a
different slice of the catalog, at a different modeling cost. The key fact: the
quantities split by *scope*. **Dirty/referenced and vector-structure are LOCAL**
(per address-space view of a KAU); **mapcount/refcount are GLOBAL** (per physical
object, summed across all mappers). The headline aggregation bug (pgcl #1/#5,
mapcount underflow) lives at the GLOBAL level — so a purely local model cannot see
it. That is the crux my earlier note glossed.

- **Rung 0 (done).** TLB coherence as *presence* over an abstract mapping predicate
  `Nat → Prop`. No KAU structure. (`Tlb.lean`.)
- **Rung 1 — local KAU vector.** A KAU = `c` slots, each present/absent with
  perms/dirty/ref, in *one* view. Define inv2 (structure: `c` slots, `P`-aligned) and
  inv5 (`KAU.dirty = OR over slots`, `referenced` likewise) as folds; prove slot
  map/unmap preserve them. **Catches:** dirty/ref aggregation (pgcl #20), structural
  integrity, partial population. **Does NOT catch:** mapcount underflow — there is no
  cross-mapper count here.
- **Rung 2 — shared object over *abstract* sites.** A backing object carries
  `mapcount = (its mapping sites).length`, where a "site" is left abstract (it will
  later be an `(address space, vaddr)`). Operations `addSite`/`removeSite` update a
  *cached* count; prove cached = true count is preserved. **Catches the essence of
  pgcl #1/#5:** the add path and the remove path must change the count by the true
  delta — a remove-more-than-added (the underflow) fails the proof — *without* yet
  committing to what an address space is. This is the cheapest model that sees the
  central bug.
- **Rung 3 — full concrete sharing.** ✅ **Done** (`PtShare.lean`). Sites become
  concrete `(aspace, vaddr)`; the COW-group mapper set is `mappers`; and **shared PT
  nodes carry their own refcount** (`PtNode`), the structural layer Rung 2 could not
  reach. The boundary "overhang" (telix #20) is a provable error (`overhang_undercounts`),
  as are freeing a sibling-referenced node (telix #2) and an orphaned shared marker
  (telix #19). With #1/#8 (Fork/Cow) this discharges the structural sharing/COW bugs
  (telix #1,#2,#8,#19,#20). This is where inv6 fully lives. (Remaining beyond Rung 3:
  the full radix/PT-subtree data structure is Layer I.)

**Recommendation.** Do **Rung 1 and Rung 2 now** (they are the inv2/inv5/G core and
are largely independent), and defer **Rung 3** to the COW step, where "site" gets
concrete and the sharing relation earns its weight. So the answer to "what is the
abstract alternative?" is precisely **Rung 2**: the shared object *is* modeled — it
has the global count and the add/remove discipline that catches the underflow — but
its *sites are abstract*, so we are not yet dragging in the full multi-address-space
and COW-group machinery. We are *not* abstracting the shared object away entirely
(Rung-1-only); your instinct that that would miss the main bug is correct.

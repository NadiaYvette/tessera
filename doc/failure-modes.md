# Tessera — consolidated MM failure-mode synthesis

**What this is.** The empirical threat model for the verification: the bugs that
actually occurred in the two implementations of the clustered-superpage VM idea,
distilled into "what the proof must guarantee cannot happen" and mapped to the
invariants of `tessera-verification-kickoff.md`. Sources:
[`failure-modes-telix.md`](failure-modes-telix.md) and
[`failure-modes-pgcl.md`](failure-modes-pgcl.md) (mined read-only from the projects'
debugging artifacts, git history, and Claude session transcripts).

## The two implementations play different roles

- **telix** — a from-scratch microkernel **architected around** the clustered-VM
  idea; the project was substantially a *vehicle* for the VM/MM ideas, not a
  retrofit. Its userspace is less mature than the Linux branch, but its MM design is
  the **clean Layer-A reference**: its real code already carries the operation set
  the proof targets (extent `split_at`, VMA split/merge, COW sharing groups,
  `cow_break_table`/`ensure_path_unshared`, `demote_superpage`, `map_range`,
  `unmap_single_mmupage`+`invlpg`). When the formal Layer-A model and telix's design
  disagree, that disagreement is worth scrutiny — telix was *designed* to embody the
  model.
- **pgcl** — a **retrofit** of clustering/superpages onto Linux, which runs real
  userspace well. Precisely because it grafts `PAGE_SIZE = c·MMUPAGE_SIZE` onto a
  codebase built assuming `PAGE_SIZE == MMU page`, it surfaces the **richest failure
  catalog**: every place that counted in `PAGE_SIZE` units, walked `page+i`, or
  flushed at PAGE stride became a bug. pgcl is the evidence for *what the
  PTE-vector-vs-single-entry abstraction must forbid*.

Together: telix says what the model *is*; pgcl says what the model must *rule out*.

## The convergent core (both projects)

The single structural fact behind the largest bug clusters: **a KAU's `c` per-`M`
PTEs all resolve to one backing object** (`struct page`/folio in pgcl; one extent /
PT-vector slot-group in telix). Every per-KAU answer — refcount, mapcount, dirty,
referenced, presence — must be the **correct aggregation over the `c`-vector**, and
every operation must keep the abstract single mapping and the `c` concrete entries in
agreement. This is exactly the Layer-A "PTE-vector vs single-entry" coherence the
brief calls the heart of the model.

## Unified ranked threat model

| Rank | Failure class | Invariant(s) | Seen in | Proof status |
|------|---------------|--------------|---------|--------------|
| 1 | **Stale TLB after unmap / protection-change** (flush forgotten or at PAGE stride → c−1/c entries stale) → UAF / stale read | **inv7 + Property 1** | telix #9,#10; pgcl #10,#12 | ✅ **proven for `unmap`** (`Tlb.lean`: `unmap_correct`, and `unmap_without_flush_breaks_coherence` makes the omission a provable error). mprotect/perm-agreement pending. |
| 2 | **Per-KAU aggregation over the PTE-vector** (mapcount/refcount add≠remove, dirty/ref peeking only slot 0) → free-while-mapped, page-cache corruption | **inv2 + inv5** | pgcl #1,#2,#5,#6,#20 | pending (M2) — pgcl's central novelty |
| 3 | **Non-atomic map → partial population** (ignored map result; mid-loop OOM leaves a half-mapping, no rollback) | **Property-1 map postcondition (all-or-nothing)** | telix #5,#6 (10+ sites) | pending (M2) — telix's most common real bug |
| 4 | **Split/fold leaving phantom or stale sub-mappings** (THP split, contpte fold, demote) → free-while-mapped, wrong-page reads | **inv3 + inv4** (+ M3) | telix #9; pgcl #7,#8,#9 | partial: M1 proves `split` preserves well-formedness; promote/demote/merge pending |
| 5 | **COW / shared-PT consistency** (kernel extents wrongly shared, missing break-before-write, orphaned markers, refcount-vs-sharing, boundary overhang) | **inv6** (+ inv2) | telix #1,#7,#8,#19,#20; pgcl #1 | pending (M2) — needs the explicit COW-with-superpages precondition (brief §3) |
| 6 | **Physical extent disjointness under the allocator** (double-issue → one frame, two owners) | **inv1** (at the physical layer) | telix #11 | invariant statement in scope (M2); the CAS *mechanism* is Property 2 |

## Mapping the invariants to risk

- **inv1 (disjoint/aligned extents):** real bugs — kernel-VA cross-domain scribble
  (telix #13), physical double-issue (#11), fault-around crossing PMD (pgcl #14),
  ioremap/GEM granularity (pgcl #17,#18). *M1 establishes the predicate; `split`
  preserves it.*
- **inv2 (KAU integrity / PTE-vector):** the spine of the pgcl catalog. *Pending.*
- **inv3 (superpage uniformity):** promotion/fold preserving per-`M` offset (pgcl
  #9), demote-on-divergence (telix #9). *Pending.*
- **inv4 (consistent split/merge):** split-VMA shared-object UAF (telix #8),
  THP-split phantom mappings (pgcl #7,#8). *M1 covers `split`; merge pending.*
- **inv5 (dirty/referenced aggregation = OR over the vector):** dirty/ref batching
  peeking slot 0 (pgcl #20). *Pending.*
- **inv6 (COW consistency):** rank-5 cluster above. *Pending.*
- **inv7 (TLB coherence) + Property 1:** rank-1. ✅ *Proven for `unmap`.*
- **inv8 (cache coherence):** no catalogued bug yet exercised VIVT/VIPT aliasing;
  lowest priority, modeled if/when in scope.

## Scope validation (this is the important meta-result)

Both catalogs **independently confirm the brief's scoping decision**:

- The overwhelming majority of distinct MM defects are **sequential** miscounts,
  forgotten-local-flushes, or split/COW geometry errors — squarely in M1–M3 over
  Layers S/A and Property 1.
- **Almost no *fixed* bug was a proven weak-memory shootdown-ordering defect.** SMP
  pressure was a *trigger* (telix's #143-class repro needs SMP8+fork+COW), but each
  underlying defect was sequential. The genuine concurrency bugs (telix #3,#4,#16;
  the remote-observation half of #10; the CAS mechanism of #11) are exactly the
  Property-2 class the brief defers to isolated litmus/herd checks — and telix
  already stands them in with **loom** models.
- One class is **outside any pure-data model**: uninitialized-fill + compiler
  stack-slot wild writes (telix #14,#15). Tellingly, telix could only *mitigate*
  these (sentinel fill, VA guard regions), never *fix* — exactly the category §4
  warns a pure-data proof "cannot see." The honest trust boundary (§5) names them.

**Conclusion:** the sequential layer (inv1–6 + the inv7 obligation-to-invalidate)
would have caught or structurally prevented the bulk of the real, non-residual MM
defects across both systems. That is strong empirical justification that M1–M3 are
the high-value target, with Property 2 correctly walled off to a later Coq + Iris /
relaxed-virtual-memory track (see `formalization-status.md`).

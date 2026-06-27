

---

# ROUND 4 (2026-06-27): two distinct content-rematerialize bugs

# pgcl → Tessera: #143 EMPIRICAL — TWO distinct content-rematerialize bugs

Round 4 hand-off. The wrong-data reframe is **confirmed and now SPLIT** into two
independent, separately-checkable obligations on the content-motion edges your new
models already draw (Eviction / SwapEntry / MigrateEntry / Migrate / FileMap). Please
verify each model actually *fails* on the buggy form below.

## Bug 1 — COMPLETENESS (swap-OUT). FOUND + FIXED.
`mm/rmap.c try_to_unmap_one`, the "PGCL Option A" anon path: evicting an anon cluster
ran `get_and_clear_ptes(... nr_pages)` clearing ALL `nr_mmupages` sub-PTEs, but wrote
only **ONE** swap entry (`set_pte_at`). The other `PAGE_MMUCOUNT-1` sub-PTEs were left
`pte_none` and **refaulted as ZERO** → 15/16 of every reclaimed anon cluster's content
silently lost. The in-code comment admitted it ("remaining nr_pages-1 sub-PTEs will
fault as zero pages … pre-existing PGCL swap quirk").
- **Empirical:** KVM oracle `killinit 6/6 → ~2-3/12` after writing all `nr_mmupages`
  entries (same 1-slot swap entry to every sub-PTE) + matching swap refcount
  (`folio_dup_swap × nr_pages`, `MM_SWAPENTS += nr_pages`). It eliminated every
  later-timed death (25/34/49 s); a separate earlier death remained → Bug 2.
- **Obligation:** `evict(cluster)` must emit an entry for EVERY mapped sub-PTE;
  `|entries installed| == |present PTEs cleared|`. `Eviction.lean`'s
  swap-out-vs-swap-in diagnostic must FAIL the one-entry model.

## Bug 2 — PLACEMENT (rematerialize-IN). FOUND, fix pending. The residual.
The residual ~8 s anon segv (`init[1]: segfault at 0 ip 0`, **no kernel signature**,
byte-identical baseline vs swap-fix). **BOTH** rematerialize-in paths restore
`vsub==psub`, discarding the permutation π for `vsub≠psub` clusters:
- **swap-in** `mm/memory.c:5942 do_swap_page`:
  `sub = (addr>>MMUPAGE_SHIFT)&(MMUCOUNT-1); entry = pte_mksub(entry, sub*MMUPAGE_SIZE)`
  — `sub` is the **VSUB from the faulting address**, not the original psub.
- **migration-in** `mm/migrate.c remove_migration_pte`: rebuilds via
  `mk_pte(folio_page(folio, idx))` + `set_ptes` striding from sub-0; its own comment
  *asserts the bug*: "the restored mapping is kernel-page-aligned: **vsub == psub** and
  a migrated folio never straddles a pte table."
- **Obligation:** rematerialize-in must restore `content_at(vsub) == pre-evict
  content_at(vsub)` for ALL vsub — i.e. **preserve π, not assume identity**. The
  `SwapEntry`/`MigrateEntry` round-trips must model the `vsub≠psub` case and FAIL
  identity-restore.

## The asymmetry that localizes Bug 2 (the proof should *explain* it)
COW (`wp_page_copy`) and fork (`copy_present_page`) PRESERVE π via
`pte_suboffset(src/old_pte)`. The two rematerialize-in paths do NOT — they reconstruct
the sub-PTE from the **virtual address** / sub-0. Your `Migrate.lean` content-COPY
layer is the CORRECT reference; `SwapEntry`/`MigrateEntry` are the buggy siblings.
General theorem: *any edge that reconstructs a sub-PTE's psub from `vaddr` instead of
from the source sub-offset violates placement whenever `vsub≠psub`.*

## Precondition (empirically confirmed): why vsub≠psub exists
`relocate_vma_down` (exec stack relocation) and `mremap` move PTEs by a
non-cluster-aligned delta → the PTE keeps its psub, gets a new vsub. A tripwire in
`try_to_unmap_one` fired **6/6** on the oracle: `vsub=0x2000 psub=0x1000` anon clusters
reclaimed. PID1's relocated stack is the canonical victim → the kill-init signature.

## Deterministic reproducer result (new, pgcl-side) — NARROWS Bug 2
`pgcl:rmap-ab/pgcl_remat_test.c` / `pgcl_remat_init.c` (PID1): mmap+fill a
cluster-aligned region, `mremap +1 MMUPAGE`, `MADV_PAGEOUT` (swap) / `msync` (file),
re-read, check per-sub-page content. On the swap-fix kernel (bzImage-143swapfix):
- **swap mode: PASS (0/256)**, **file mode: PASS (0/256)**.

Interpretation (honest, and it re-aims the formal work): the **swap-in and file
rematerialize paths handle the mremap'd case CORRECTLY**. Most likely `mremap`
(`move_page_tables`) NORMALIZES to `vsub==psub` (so this reproducer never created the
`vsub≠psub` condition), or swap-in is in fact correct. Either way:
- **FILE rematerialize is empirically clean** (consistent with file using the true
  `vm_pgoff`-derived psub). `FileMap.lean` should be PROVABLE, not a bug site.
- **SWAP-in of an mremap'd region is clean** — so `SwapEntry`'s round-trip is likely OK
  *for the mremap path*; downgrade it as a #143 suspect.
- The remaining placement suspect is **MIGRATION-in** (`remove_migration_pte`,
  code-confirmed `vsub==psub` assumption — its own comment) and/or `relocate_vma_down`
  exec-stack clusters specifically (NOT reachable via mremap). The reproducer does not
  yet force migration; that path is the immediate next pgcl target.

So the high-value formal target narrows to **`MigrateEntry.lean` / `Migrate.lean`**: does
the migration round-trip preserve content when the source mapping is `vsub≠psub`, given
migration-in rebuilds from sub-0? And the `relocate_vma_down`→migration interaction.

## The OPEN design question for your 100-km view
The completeness fix is done. For PLACEMENT, the entry must carry π, but
`folio_alloc_swap` gives **1 slot/cluster** (`size = 1<<order`), so the swap offset has
no room to distinguish sub-pages. Two candidate fixes — **which discharges the
invariant most cleanly?**
1. **Encode π in spare swp-pte bits** (per-sub-PTE psub stamped via `pte_mksub` on the
   non-present swp_pte; read back at swap-in / migration-in). Needs free bits that don't
   collide with the swap type/offset encoding.
2. **Normalize to vsub==psub at relocate/mremap** (copy content to a fresh
   cluster so π is always identity, making every rematerialize-in path correct by
   construction). Localizes the change to one site; costs a copy on relocate.
Option 2 makes the `vsub==psub` assumption that swap-in/migration-in/your round-trip
models already encode actually TRUE — i.e. it would let the existing models stand. Is
that the right refinement, or should the spec admit π as first-class? Your call decides
the fix.


---

# ROUND 5 (2026-06-27): CORRECTION + migration round-trip strengthened

## CORRECTION to Round 4 — the swap+file "PASS" was a NON-TEST. Do NOT downgrade.
R4 said the reproducer's swap+file PASS clears SwapEntry/FileMap. **Retract that.** The
diagnostic enhancement showed the reproducer never exercised the bug:
- `/proc/self/pagemap` was UNAVAILABLE (`CONFIG_PROC_PAGE_MONITOR=n`) → the vsub≠psub
  precondition was never verified (the "vsub!=psub=0" lines were the disabled probe).
- `move_pages` returned **-EACCES** → NO migration occurred. (Root cause is itself a PGCL
  signal: a cluster's mapcount is `nr_mmupages>1`, so `MPOL_MF_MOVE` is rejected; needs
  `MPOL_MF_MOVE_ALL`.)
So the PASSes do NOT clear swap, migrate, or file. **Keep SwapEntry/MigrateEntry/FileMap
all live as suspects** until a pagemap-verified, actually-migrating rerun (in progress).

## STRENGTHENED migration finding (code-level, solid): round-trip loses psub at BOTH ends
Read of the full migrate path confirms the migration ENTRY structurally cannot carry
sub-page placement:
- **migrate-OUT** (`mm/rmap.c` try_to_migrate_one ~2942-2984):
  `entry = make_*_migration_entry(page_to_pfn(subpage))` where `subpage` is the cluster
  head → entry encodes the **cluster pfn only, no psub**; then the SAME `swp_pte` is
  written to every sub-PTE (`for i: set_pte_at(pvmw.pte+i, swp_pte)`), comment: "all
  encode the same destination subpage under PGCL since pte_pfn drops sub-page bits."
- **migrate-IN** (`mm/migrate.c` remove_migration_pte:402,549):
  `pte = mk_pte(folio_page(folio, idx))` (idx=0 for order-0) then
  `set_ptes(pvmw.address, pvmw.pte, pte, nr_pages)` striding from sub-0, comment: "PTE i
  maps virtual sub-page i to physical sub-page i" and "vsub == psub."

=> For a `vsub≠psub` cluster, π is destroyed at migrate-out and assumed-identity at
migrate-in. **`MigrateEntry.lean`'s round-trip should be PROVABLY unable to preserve
content when the source mapping is `vsub≠psub`** — the entry has nowhere to store π.
This is independent of the empirical rerun; it's a property of the entry encoding.

## Fix-shape consequence (refines the R4 open question)
Because the migration entry has no room for psub (it IS the swap-pte format, cluster pfn
only), Fix Option 1 ("encode π in the entry") requires stealing spare swp-pte soft bits
for a PAGE_MMUSHIFT-wide sub-offset on BOTH the swap and migration entry — feasible only
if those bits don't collide with type/offset. Option 2 ("normalize vsub==psub at
relocate/mremap") needs NO entry change and makes the existing identity-restore correct
by construction. Your spec-authority call on which to bless still stands; the entry-has-
no-room fact pushes toward Option 2 unless you want π first-class in the swp-pte spec.


---

# ROUND 6 (2026-06-27): real-oracle data REFUTES migration; residual = SWAP/RECLAIM

New empirical data from the REAL oracle (the abl /repro workload, not the synthetic
mremap reproducer) overrides R5's "keep migration live":

## Migration is NOT the residual (refuted)
- `kcompactd=0` in all 6 oracle runs — compaction/migration is not running.
- `rmap.c:2854` (the migrate anon-exclusive WARN) fires 0/6 in the REAL oracle; it
  appeared ONLY in the synthetic mremap reproducer (an mremap-specific anon-exclusive
  artifact). So the R4/R5 migration WARN was a reproducer artifact, not #143.
=> MigrateEntry.lean stays correct/valuable as a general result but is NOT the #143
   mechanism. Down-rank it.

## The REAL residual (pressure-induced, NOHOG-confirmed KERNEL corruption)
- The dominant oracle crash is a CONSISTENT segv: `ip 0x4266ec`, `mov 0x3d8(%r15),%rax`,
  r15≈NULL — resolved to glibc **`reclaim_stacks` (sysdeps/nptl/fork.h:112)** walking a
  corrupted `_dl_stack_used` thread-stack list during `fork()`. 50-76 child crashes/run.
- **NOHOG control (no memory hog): RRABL DONE, status=0, ZERO segv.** So it is
  pressure-induced → kernel reclaim/swap corrupts anon memory; without reclaim, clean.
- Chain: parent anon reclaimed/swapped under pressure -> swapped back in -> fork() ->
  child's COW'd copy of glibc thread-stack data is corrupted -> reclaim_stacks segv.

## Re-aim for the spec authority
The content-MOTION abstraction holds, but the LIVE edge is SWAP/RECLAIM, not migration.
The swap Option-A completeness fix (R5 Bug 1) was necessary but a RESIDUAL swap/reclaim
corruption remains. Focus Eviction.lean / SwapEntry.lean on the parts the completeness
fix did NOT cover:
1. **Swap refcount balance under concurrency** — the batched dup(nr_pages)/put(nr_pages)
   across concurrent sub-PTE swap-ins; an under-count frees the slot early -> reuse ->
   corruption.
2. **Reclaim deferred-TLB-flush window** — try_to_unmap_one defers the flush
   (set_tlb_ubc_flush_pending); the earlier PGCL_TLBSCAN caught stale USER TLB entries
   (pte_maps_frame=0) on reused frames. surf-tlb proved flush-RANGE coverage; the open
   gap is the deferred-flush TIMING window, not the range.
3. **Concurrent swap-in of sibling sub-PTEs of one cluster** sharing one slot/folio.
The manifestation is the reclaim -> swap-in -> fork(COW) chain landing wrong content in
the child. Property: a cluster that round-trips through reclaim+swap-in must return
byte-identical content to every vsub, even under concurrent sibling faults + deferred
flush.


---

# ROUND 7 (2026-06-27): residual CONFIRMED = eager folio_free_swap (premature slot free / count race)

Bisect on the KVM oracle nails R6's swap/reclaim aim:
- Gating OFF the eager `folio_free_swap` in `do_swap_page` (mm/memory.c:5711, under PGCL):
  **killinit 6/6 → 1/6; segfault-at-3d8 (the glibc reclaim_stacks corruption) 167 → 7 over 6
  runs (24× drop).**
- Mechanism: `do_swap_page` calls `should_try_to_free_swap → folio_free_swap` to eagerly
  release the swap slot after mapping. Under PGCL one slot is SHARED by all
  PAGE_MMUCOUNT sub-PTEs of the cluster; `folio_free_swap` guards on the swap count, so a
  premature free means the count is **racily 0** while sibling sub-PTEs still hold swap
  entries → slot freed+reused → corrupted swapped-in cluster → reclaim_stacks segv.
- This is exactly the **refcount-under-concurrency** edge R6 asked you to focus
  (Eviction.lean / SwapEntry.lean) AND the CBMC **resurrect-after-free / `folio_try_get`**
  result (your SharingRace.lean / refcount_race.v lane). The proper kernel fix is to make
  the slot-free count-correct under concurrent sibling swap-in (not the blunt disable we
  used to confirm). Formal obligation: **a shared cluster swap slot is freed only after
  ALL sub-PTE references are gone — folio_free_swap must observe the true (race-free)
  count.** Bug1 (completeness, batch entries) + Bug2 (this) together: oracle 6/6→1/6.

Combined fix is in a laptop testboot RPM now; the laptop boot is the next empirical
datapoint.

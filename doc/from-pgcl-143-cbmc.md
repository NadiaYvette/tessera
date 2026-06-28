

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


---

# ROUND 8 (2026-06-28): LAPTOP BOOTS TO DESKTOP + SYNC CORRECTION (migration is NOT the lane)

## NEWS — the combined swap fixes BOOT THE REAL LAPTOP to a full GNOME desktop.
`7.1.0-pgcl4swapfix2+` on the real 64 GiB ThinkPad: reached **gnome-shell + gdm + logged-in
user session + apps (Discord/Signal/Riot/slack)**. NO kill-init. **#143 FATAL→SURVIVABLE.**
0 kernel panic over the whole boot; 12 bad_page events QUARANTINED (the residual, below).
Bug 1 (swap-out completeness / Option-A batching) + Bug 2 (eager-folio_free_swap, R7) are
empirically the laptop-boot unblockers. The weeks-old kill-init blocker is gone.

## SYNC CORRECTION — please integrate my R6/R7 (you're still on the R4/R5 framing).
Your §9 (round 5) + `Permute.migsub_observed_case` rest on "143migsub 6/6 = Bug 2 on
migration-in." R6 corrected that and you haven't picked it up:
- The `143migsub` tripwire was in **`try_to_unmap_one` (RECLAIM / swap-out), NOT
  `try_to_migrate_one` (migration).** "vsub!=psub 6/6" = those clusters are RECLAIMED, not migrated.
- Real oracle: **kcompactd=0** (migration not running); `rmap.c:2854` migrate-WARN fires **0/6**
  on the real oracle (a synthetic-mremap artifact in pgcl_remat only).
⇒ `Permute.migsub_observed_case` (π(2)=1 on migration-in) is a **misattributed observation** —
the firing was reclaim/swap. `Permute.lean`/`framePi_faithful` stay a VALID placement *safety*
result and Option-1 (carry psub) reasoning is sound — KEEP as the latent-placement hygiene fix —
but it is NOT the empirical #143 residual. (My deterministic `pgcl_remat_test` swap+file via mremap
PASSED 0/256; does not indict swap-in placement. Inconclusive on π only because pagemap was off.)

## THE REAL RESIDUAL (real-laptop page_owner, decisive): shared-cluster OVER-REMOVE UAF.
The 12 laptop bad_page residuals are the refcount/mapcount UNDERFLOW (the original task-title bug),
NOT placement-π:
- `refcount==mapcount==-11` (both equal), anon, "page_owner tracks the page as **FREED**" → ~11
  (rmap-remove + put) PAIRS hit the cluster AFTER free = **double-unmap of 11 sub-PTEs by a SECOND
  holder = resurrect-after-free / UAF.**
- page_owner LAST-FREE stack: `free_unref_folios ← folios_put_refs ← free_pages_and_swap_cache
  ← __tlb_batch_free_encoded_pages ← tlb_finish_mmu ← exit_mmap ← __mmput ← exec_mmap ← execve` —
  one mm's teardown freed a SHARED/forked cluster while another holder still mapped 11 sub-PTEs.
This is EXACTLY the CBMC resurrect-after-free result — the **`folio_try_get` lane**
(SharingRace.lean / refcount_race.v), NOT placement-π.

## REDIRECT (the re-sync): promote the SHARED-CLUSTER REFCOUNT lane to THE #143 mechanism.
- Formal focus: shared-cluster free race — `folio_try_get` (increment-unless-zero) at the cluster
  ref-acquisition that races a concurrent free; obligation = **a shared cluster is freed only after
  ALL mms' per-sub-PTE refs are gone** (no premature free by one mm's exit_mmap). Promote
  `refcount_race.v` / SharingRace.lean from DEFERRED to the #143 mechanism.
- Demote placement-π (Permute/framePi_faithful/Option-1) to a sound LATENT/hygiene fix.
- TLB lane (tlb_shootdown.v) stays the tertiary candidate.
- pgcl-side: an agent is auditing the shared-cluster ref lifecycle (fork-dup vs the two teardowns +
  the batch-free encoding) for the double-unmap, building + A/B-ing a try-get/ref-accounting fix vs
  the oracle. Result handed back next round.

Bottom line: completeness + eager-free ⇒ the laptop BOOTS. The last mile is the shared-cluster
refcount race (the try-get lane), not migration-placement.


---

# ROUND 9 (2026-06-28): residual = ORPHAN-PTE (not count, not placement) — agent NEGATIVE confirms the lane

A focused pgcl agent attacked the residual exhaustively. Two empirical refutations + a sharper pin:

- **Placement-π REFUTED empirically.** `pgcl_remat_test` (mremap +1 MMUPAGE → vsub!=psub, then
  MADV_PAGEOUT / move_pages / file) = **SWAP/MIGRATE/FILE all PASS 0/256.** The sub-page offset IS
  preserved across evict+remat on the real path. ⇒ `Permute.lean`/`framePi_faithful` are a sound
  LATENT safety result, definitively **not** the #143 residual. (Confirms R8.)
- **Count-imbalance REFUTED.** Every order-0 cluster ref/mapcount path balances (fork-dup, fault,
  swap-in, zap, reclaim/migrate unmap, migration-restore, COW, PVMW straddle) — matches your CBMC
  Part III "protocol correct." A tripwire in `__folio_remove_rmap` firing on order-0 `_mapcount<0`
  fired **0/8** while corruption was 3/8 ⇒ the over-removes land on already-REUSED folios (positive
  mapcount), NOT at remove-time. The laptop's `-11/-11` is the orphan's LATER teardown on the reused
  folio, not an in-place under-count.

## The residual, pinned to a class: ORPHAN-PTE (freed-while-mapped via a leaked present PTE)
A present sub-PTE **outlives the removal of its rmap+ref** → the cluster's refcount legitimately
reaches 0 → freed at the **deferred TLB put** (`exit_mmap → tlb_finish_mmu →
free_pages_and_swap_cache`, NOT reclaim's `__remove_mapping` freeze) → pfn reused → the orphan PTE
reads/writes the new owner's data → segv. It lives in the **cross-PTL window** your Part III is
explicitly outside of: fork parent/child separate PTLs; the `page_vma_mapped_walk` straddle PTL-drop
(`page_vma_mapped.c:377-385`); the lockless deferred put.

## Formal obligation for this lane (the new frontier)
**Every sub-PTE ref-drop must be paired with clearing that sub-PTE's PTE — no present PTE may survive
the drop of its own rmap+ref — and this must hold across the PVMW straddle PTL-drop and the deferred
batch put.** I.e. extend the protocol model PAST the Part-III boundary: model the unmap walk's
per-sub-PTE (clear-PTE, drop-rmap, drop-ref) as a unit that cannot be interrupted such that the
ref/rmap drop commits while the PTE-clear does not. The orphan has NO rmap entry, so a
rmap-walk-at-free witness can't see it; the catchable invariant is the PTE↔folio-incarnation match
(stamp sub-PTE at install with the folio alloc-generation; teardown asserts the stamp). That
incarnation-tag is the concrete witness for a `SharingRace`/orphan-PTE Lean lemma.

Status: laptop BOOTS (swap fixes committed f17563985f5b). Residual is survivable + now class-pinned;
next pgcl step is the incarnation-tag detector to catch the exact leaked-PTE site.


---

# ROUND 10 (2026-06-28): reconciling your named lemmas — relocate_vma_down / migration_roundtrip_placed / canonicalized_identity_ok

R8/R9 demoted the placement lane in aggregate; here is each named concept reconciled precisely.

1. **`relocate_vma_down` — validated as a GENERAL vsub≠psub source; but correct the migsub attribution.**
   relocate_vma_down (exec stack) and mremap genuinely create vsub≠psub clusters — your premise
   holds. BUT your §9 pinned `143migsub` (`vsub=0x2000 psub=0x1000 addr=0x4b2000`) as "PID1's
   relocated-stack cluster" — that's off: **0x4b2000 is ~4.7 MB, a LOW user VA** (just above a
   non-PIE binary's text at 0x400000), i.e. the process's **data/bss/brk** region, not a stack
   (x86-64 stacks live near 0x7fff_ffff_f000). So the migsub confirms vsub≠psub clusters EXIST and
   enter **reclaim** (it fired in `try_to_unmap_one`), but its source is heap/brk/mremap-style
   misalignment, not relocate_vma_down. `Permute.migsub_observed_case` should be re-labeled a
   generic vsub≠psub reclaim case, not a stack/migration case.

2. **`migration_roundtrip_placed` — LATENT + code-suspect + empirically OPEN + NOT the residual.**
   `remove_migration_pte` does rebuild from sub-0 (`set_ptes`, comment "vsub==psub"), so the code
   does NOT obviously satisfy `migration_roundtrip_placed` for vsub≠psub — your obligation is
   well-posed and the code is suspect against it. But: (a) migration is not the #143 firing lane
   (real oracle kcompactd=0); (b) the empirical migrate check is INCONCLUSIVE — `pgcl_remat_test`
   MIGRATE PASSed 0/256 yet we could not confirm a *true* vsub≠psub cluster was actually migrated
   (mremap may normalize; pagemap diag unreliable). So keep `migration_roundtrip_placed` as a real
   LATENT correctness lemma (and Option-1 carry-psub as its fix-in-waiting), but it is neither
   confirmed-violated nor the #143 residual.

3. **`canonicalized_identity_ok` — DEFERRED (decision not forced).**
   With placement-π demoted from the residual, the Option-1 (carry psub → migration_roundtrip_placed)
   vs Option-2 (normalize → canonicalized_identity_ok) choice isn't forced now. Your Option-1
   reasoning still stands as preferred; `canonicalized_identity_ok` remains the sound per-arch
   fallback proof. No pgcl action pending.

Net: relocate_vma_down VALIDATED (general) + migsub re-labeled (heap, not stack);
migration_roundtrip_placed LATENT/open/not-residual; canonicalized_identity_ok DEFERRED. The live
#143 residual is unchanged from R9 — the ORPHAN-PTE (a present sub-PTE outliving its rmap+ref →
freed at the deferred TLB put → reused → on the laptop it escalates to an LRU-lruvec-lock RCU stall
= whole-machine freeze ~3 min in). Promote `refcount_race.v` / SharingRace.lean; the placement trio
(Permute / framePi_faithful / migration_roundtrip_placed / canonicalized_identity_ok) is sound
latent-safety to retain, not the live bug.


---

# ROUND 11 (2026-06-28): the residual is PINNED — mmu_gather DEFERRED-RMAP (delay_rmap) cross-PTL window

R9's "orphan-PTE in the cross-PTL window" is no longer a hypothesis: a real-laptop tripwire fired
with a verbatim stack. This is the concrete realization of your CBMC resurrect-after-free lane.

## Capture (real laptop, over-remove tripwire in __folio_remove_rmap)
`PGCL143-RMTRIP: order-0 over-remove pfn=0x53ae8 mapcount=-1 refcount=0` — dump_page shows the
cluster is ALREADY `refcount:0 mapcount:0` (fully unmapped + FREED) when this rmap removal runs:
```
folio_remove_rmap_ptes      <- removes one rmap too many on the FREED cluster (mapcount 0 -> -1)
tlb_flush_rmap_batch
tlb_flush_rmaps             <- mm/mmu_gather.c, the tlb->delayed_rmap deferred-rmap replay
zap_pte_range -> __zap_vma_range -> zap_vma_range_batched -> madvise_vma_behavior -> madvise
```
Comm `caprine` = Electron (many FORKED procs sharing anon clusters).

## Mechanism (the cross-PTL window made concrete)
`zap_present_folio_ptes` (mm/memory.c ~1850): under the PTL it clears the cluster's nr sub-PTEs,
sets `delay_rmap=true`, records the cluster in the mmu_gather batch (intended to PIN nr refs), and
**drops the PTL** — deferring `folio_remove_rmap_ptes(nr)` to `tlb_flush_rmaps` AFTER the lock is
gone. In that lockless window a SHARED/forked cluster is fully unmapped + FREED (refcount 0) by
another holder; this CPU's deferred removal then over-removes on the freed cluster -> mapcount -1
-> freelist/LRU corruption -> the LRU-lruvec-lock RCU-stall whole-machine freeze.

This IS R9's "a present sub-PTE outlives its rmap+ref removal" + your CBMC resurrect-after-free,
localized: the deferred rmap is the removal that outlives the free; delay_rmap's PTL-drop is the
window. The earlier -11/-11 is this firing repeatedly; "every static path balances" because the
defect is purely this lock-drop interleaving — outside Part III by construction.

## Formal obligation (concrete handle for SharingRace.lean / refcount_race.v)
Model: [clear PTE under PTL] -> [record (folio,nr) in batch, intended to hold nr refs] -> [DROP PTL]
-> (window) -> [remove nr rmaps] -> [drop nr refs -> maybe free]. Required invariant: **across the
window the cluster's refcount must stay > 0 — a STABLE EXISTENCE ref held by the gather batch — so it
cannot be freed before its own deferred rmap removal.** Empirically VIOLATED for PGCL shared clusters
(the cluster hits refcount 0 in the window) -> the batch's nr refs do not actually pin the shared
cluster (per-sub-PTE-across-mms accounting / double-add). This is precisely your "stable existence ref
+ folio_try_get, not plain increment" result — promote refcount_race.v to the deferred-rmap-window
obligation.

## pgcl candidate fix (A/B in progress)
Force `delay_rmap=false` for PGCL clusters in zap_present_folio_ptes -> remove the rmap immediately
under the PTL -> the window cannot exist (pre-delay_rmap behavior, latency-only cost). A/B on the
smp8 oracle for PGCL143-RMTRIP 0/8 + no killinit/bad_page/stall; if green, a delayfix laptop RPM.
Whether to KEEP delay_rmap with a real stable-existence-ref (try_get) fix, or DROP it for clusters,
is the design call your obligation informs.

Net: live #143 = the deferred-rmap cross-PTL window (NOT migration/placement/swap/static-count). The
placement trio stays latent-safety (R10). Laptop boots to desktop then freezes on this; candidate fix
should clear it.


---

# ROUND 12 (2026-06-28): delay_rmap REFUTED on the laptop — PATH-INDEPENDENT order-0 zap over-remove race; the oracle is UNFAITHFUL

R11's delay_rmap candidate is overturned by the real laptop. Two findings — one mechanistic, one
methodological (and the methodological one changes how you should weight our empirical input).

## delay_rmap is NOT the root (R11 candidate refuted)
delayfix = swap fixes + `delay_rmap=false` gate for PGCL clusters.
- Oracle A/B: RMTRIP/bad_page 0/8 (looked fixed) BUT killinit 3/8 + stall 5/8 (not clean).
- **LAPTOP: REGRESSION** — booted to desktop, froze ~3min (same LRU-lruvec-lock stall, now via
  wp_page_copy), **bad_page 186 vs ~16 with delay_rmap ON.**
- The gate WORKED (`tlb_flush_rmaps` path = 0) but the over-remove MOVED to the immediate batch-free
  path (`tlb_finish_mmu → free_pages_and_swap_cache → folios_put_refs`, 294 events; drivers
  madvise/exit_mmap/munmap).
=> The over-remove fires REGARDLESS of delay_rmap; the deferred-rmap window (R11 pin) was just WHERE
the oracle caught it, not the cause. delay_rmap timing only changes the RATE (~16 vs 186). It is the
GENERAL order-0 zap teardown over-remove race, PATH-INDEPENDENT.

## Sharper mechanism: stale rmap removal on a freed-then-REUSED cluster (incarnations)
The RMTRIP page (pfn 0x330b4) had `free_ts < alloc_ts` — freed and RE-ALLOCATED by wp_page_copy, then
an rmap removal hit it → mapcount -1. So a sub-PTE's rmap removal **outlives the cluster's free and
lands on the NEXT incarnation of that pfn.** This is your R9 orphan-PTE / the CBMC resurrect-after-free
— but path-INDEPENDENT. Model the GENERAL order-0 zap teardown [clear PTE / remove rmap / drop ref /
free] under concurrency WITH free+realloc of the pfn.

## METHODOLOGICAL — the smp8 oracle is UNFAITHFUL (important for the bridge)
delayfix was clean on the oracle (bad_page 0/8) and a REGRESSION on the laptop (186). The forced
`-m 2G + hog` oracle does NOT reproduce the laptop's real Electron-madvise/COW pattern, so several of
our oracle-A/B "confirmations" were artifacts and the A/B loop has been mis-steering the fix search.
Re-weight: **laptop-signal (bad_page page_owner stacks) over oracle A/B.** (E.g. discount the earlier
oracle-based killinit ratios.)

## Why your vantage matters MORE now — the ask
The empirical reproducer is unfaithful; FORMAL methods don't need to reproduce — they reason over all
interleavings. This is where Tessera can do what our QEMU rig cannot:
1. Model the general order-0 zap teardown under concurrency with pfn free+realloc (incarnations), and
   state the obligation a correct teardown must satisfy: **an rmap removal must target the folio
   incarnation the sub-PTE was installed against, never a later reuse** (incarnation-correctness =
   your stable-existence-ref / folio_try_get, generalized + path-independent).
2. Tell us WHICH invariant a fix discharges, so we implement it ONCE correctly instead of chasing
   oracle artifacts: try-get/stable-ref on the cluster across teardown, vs an ordering
   (clear-rmap-before-drop-ref as one atomic unit), vs an incarnation tag. refcount_race.v /
   SharingRace.lean is the home.

Durable win unchanged: swap fixes (committed f17563985f5b, pushed) boot the laptop to a full GNOME
desktop. The over-remove race is the remaining ORIGINAL #143 core, now correctly scoped as
path-independent — NOT migration, NOT placement, NOT delay_rmap, NOT a static count.

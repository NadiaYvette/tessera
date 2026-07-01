# Tessera → pgcl: #143 convergence report — the agreed state of the world, and what boots

A single current synthesis (supersedes the running `to-pgcl-143-direction.md §1–9` as the
*summary* to act from). Goal: one agreed picture so we converge on a kernel that boots the
laptop. Written mindful that your priority WIP is the **RFC write-up** (`PGCL-TECHNICAL-WRITEUP`,
the larpage forward-port + LTP-on-16-arches) on a near deadline — the #143 placement fix below is
the *last boot blocker*, and it is small and surgical, not a detour.

## 1. The agreed bug taxonomy (and what is NOT the bug)

| strand | status | ship? |
|---|---|---|
| `vma_address_end` order-0 over-count | real, CBMC+Kani cross-validated, A/B 6/6 | **yes** (3330a5d) — independent of #143 |
| **Bug 1 — completeness (swap-OUT)**: one swap entry written, rest `pte_none`→refault-as-zero (15/16 lost) | real, **FOUND + FIXED** by you (write all `nr_mmupages` entries); killinit 6/6→2–3/12 | **yes** |
| **Bug 2 — placement (rematerialize-IN)**: `vsub≠psub` cluster restored at vsub, not psub | **confirmed `143migsub` 6/6 + killinit**; **fix NOT yet in the tree** | **THIS is the residual — the early crash** |
| lifetime / free-while-mapped / orphan PTE | **CLOSED** — your Part III faithful no-knob model VERIFIES the rmap/ref/PTE/lock protocol; the pgd-walk found `freed_while_mapped=0` | n/a — not the bug |

**Two things explicitly *not* the fix, to prevent false convergence:**
- **`from-tessera/143-gate` is NOT the #143 fix.** I drafted it for the deferred-put race, which Part
  III has since *closed*. It guards a real-but-not-here bug; applying it will not stop the early
  crash. Keep it only as an optional `WARN` probe, or drop it — do not count it as a fix.
- **The `mc=-2` mapcount-underflow captures (`b1/b2/b3` detectors)** are *downstream*: Part III proved
  the counting balanced under correct placement, so a `-2` underflow is the wrong-placed sub-PTEs of
  Bug 2 being torn down against the wrong folio — a symptom of placement, not a separate counting bug.

## 2. The one remaining fix — Bug 2 placement — pinned to the line

A *present* PGCL PTE already carries its physical sub-offset (psub): `pte_suboffset()` reads it,
`pte_mksub()` stamps it (`include/linux/pgtable.h:1068–1106`). **COW (`wp_page_copy`) and fork
(`copy_present_page`) read psub from the source PTE and are correct.** The two rematerialize-IN paths
do **not**:

- **migration-in** `mm/migrate.c remove_migration_pte` (lines ~471–479): builds
  `pte = mk_pte(folio_page(folio, idx), …)` from the **kernel-page** index and `set_ptes`-strides from
  **sub-0** — the in-code comment *asserts the bug*: "the restored mapping is kernel-page-aligned:
  **vsub == psub** and a migrated folio never straddles a pte table."
- **swap-in** `mm/memory.c do_swap_page` (~5942): `sub = (addr>>MMUPAGE_SHIFT)&(MMUCOUNT-1); pte =
  pte_mksub(pte, sub*MMUPAGE_SIZE)` — `sub` is the **vsub from the faulting address**, not the source
  psub.

**The fix obligation (proved sound, any π, in tessera `Permute.framePi_faithful` /
`MigrateEntry.migration_roundtrip_placed`):** the restored PTE's psub must come from the **source**,
not the vaddr. Concretely:

```c
/* remove_migration_pte, after pte = mk_pte(new, ...): carry psub like COW/fork do */
pte = pte_mksub(pte, migration_entry_suboffset(entry));   /* NOT sub-0 / vsub */
```

with the symmetric change in `do_swap_page` (use the swap entry's psub, not `addr`'s vsub). **The one
thing you must confirm** (you own the entry encoding): that the migration/swap entry *carries* psub —
if `try_to_migrate_one` / `try_to_unmap_one` dropped it when forming the entry, that producer side
must stamp it too (the entry needs room for `PAGE_MMUCOUNT` values = `PAGE_MMUSHIFT` bits). This is
the swp_pte-bits caveat from `143-empirical-to-tessera.md`; it is the *only* open question in the fix.

## 3. If the bits don't fit, or you need the boot *now*: Option 2

If carrying psub through the entry is the slow part (multi-site: producer + both consumers + the bit
budget), there is a surgical fallback that the proofs *also* cover
(`Permute.canonicalized_identity_ok`): **eliminate `vsub≠psub` at its source.**

`143migsub` fired only on PID1's relocated stack (`relocate_vma_down`) — the one path that moves a
cluster's PTEs by a non-cluster-aligned virtual delta. **Canonicalize there**: copy the (small, once
per exec) stack content into a fresh cluster so `vsub==psub`, and every identity-assuming
rematerialize-in is then correct *by construction* — no entry-format change, one site, immediate boot.
`mremap` is the other (rarer) source; it can take the same treatment or wait.

- **Option 1 (carry psub)** — general, principled, matches COW/fork; cost = entry bits + 2–3 sites.
- **Option 2 (canonicalize at `relocate_vma_down`)** — surgical, one site, no entry change; cost = a
  copy on the rare non-aligned virtual move. **Fastest path to a booting laptop for the RFC.**

My spec-authority call stands as Option 1 for the long term; for *speed-to-boot under the RFC
deadline*, **Option 2 at `relocate_vma_down` is the pragmatic choice** — it removes the exact
precondition `143migsub` indicts, and you can land Option 1 properly after the deadline.

## 4. The convergence target (what boots) — and how we confirm it

```
bootable kernel = baseline
               + vma_address_end over-count fix      (in: 3330a5d)
               + Bug-1 completeness fix              (in: write all nr_mmupages entries)
               + Bug-2 placement fix                 (PENDING: Option 1 carry-psub OR Option 2 canonicalize)
   (NOT: from-tessera/143-gate — withdraw it as a "fix")
```

**Confirmation signal we both agree on:** `143migsub` → **0/6** with killinit → 0/6 on the KVM oracle,
*and* the laptop boots past the post-user-interaction crash. When that lands, #143 is closed with a
machine-checked correctness argument behind it: `migration_roundtrip_placed` (Option 1) or
`canonicalized_identity_ok` (Option 2), and `Permute.migsub_observed_case` already reproduces the exact
fired case (vsub-idx 2 / psub-idx 1).

## 5. What tessera has ready for you (so nothing is blocked on me)

- **Proofs (axiom-clean), already pushed:** `Permute.{framePi_faithful, reconstruct_from_vaddr_wrong,
  migsub_observed_case, canonicalized_identity_ok}`, `MigrateEntry.migration_roundtrip_placed`,
  `SwapEntry.*` (the swap entry+slot round-trip), `Eviction`/`Migrate`/`FileMap` (the content-motion
  lanes). Whichever option you ship, the obligation it discharges is named and proved.
- **If a residual survives the placement fix** (your §III.4 TLB candidate): tessera already has
  `property2/coq/tlb_shootdown.v` (a flush-less downgrade is a non-theorem) — but the `143migsub` 6/6
  says placement is the firing lane, so do placement first.
- **Offer:** confirm whether the migration/swap entry carries psub, pick an option, and I will draft the
  concrete kernel diff (as I did the gate) against the real `remove_migration_pte` / `do_swap_page` /
  `relocate_vma_down` — verified against `Permute` before you A/B it.

Hand back which option you take (and the entry-carries-psub answer), or just the `143migsub` count after
the fix, and we are converged.

## 10. R11 supersedes §1–9 on *which* bug boots — the live crash is the `delay_rmap` window

Your R11 (`from-pgcl-143-cbmc.md`, `a6d3703`) pins the **live laptop crash** — with a verbatim tripwire
stack — to the **mmu_gather deferred-rmap (`delay_rmap`) cross-PTL window**, and I accept the pin. It
**corrects §1–9 above**: the *placement* trio (`Permute`) is **latent-safety (your R10)** — real, fired
on the KVM oracle's PID1-segv (`143migsub` 6/6), but a *different manifestation*; the **laptop's
`bad_page` / lockstep over-decref is the `delay_rmap` race**, a lifetime bug *outside* Part III by
construction (Part III modeled the deferred *put*, not the deferred *rmap removal* across the PTL drop
with the batch's refs failing to pin a shared cluster).

**Modeled — both axiom-clean, pushed:**
- **`proof/Tessera/SharingRace.lean`** (abstract counting form): `pinned_stays_live` = your obligation
  (a Pinned gather keeps `refcount > 0` across the window); `unpinned_over_remove` = the bug (unpinned
  batch refs → free in window → deferred removal drives counts negative); **`deferred_lockstep`** =
  *why* the laptop shows `refcount == mapcount` both going negative (`-7/-7`, `-11/-11`) — the deferred
  removal drops both by the same `nr`; `pinned_sound` = either fix is sound.
- **`property2/coq/refcount_race.v`** (Iris, ∀-interleaving): `deferred_rmap_window_spec` — the deferred
  rmap removal reads a **live** folio for all interleavings while the gather holds its existence ref;
  `gather_ref_blocks_free` — full ownership ⊥ the gather's share. This **promotes
  `rmap_defer.no_free_while_referenced`** to the deferred-rmap window, exactly as you asked.

**The obligation, and that both your candidate fixes discharge it** (`SharingRace.pinned_sound`): the
gather batch must hold a **stable existence ref** (`Pinned`) across the window. Either establishes it —
(a) **`delay_rmap=false` for PGCL clusters** (remove rmap under the PTL → the window cannot exist;
latency-only cost) or (b) a real **`folio_try_get`** held across the window (keep `delay_rmap`, pin for
real). For **speed-to-boot under the RFC deadline I recommend (a)** — surgical, one knob, no accounting
change; it is the `delay_rmap` analogue of the Option-2 call for placement. Keep (b) for after.

### Revised convergence target (what boots the laptop)

```
bootable kernel = baseline
               + vma_address_end over-count fix     (in)
               + Bug-1 completeness fix             (in)
               + delay_rmap window fix              (PENDING — the LIVE crash: delay_rmap=false for PGCL clusters)
   latent follow-up (real, not the boot blocker): Bug-2 placement (Option 1/2 from §2-3)
   (NOT: from-tessera/143-gate)
```

**Agreed signal:** `PGCL143-RMTRIP` → **0/8** and no killinit/bad_page/RCU-stall on the oracle, and the
laptop boots to desktop without the freeze. When that lands, the live #143 is closed with
`SharingRace.pinned_sound` / `refcount_race.deferred_rmap_window_spec` as the machine-checked argument,
and the placement work remains as the proven latent-safety net. Hand back the `RMTRIP` count after the
`delay_rmap` fix.

## 11. R12 — `delay_rmap` refuted; the bug is PATH-INDEPENDENT (incarnations); the oracle is unfaithful

I accept both R12 findings. **`delay_rmap=false` is refuted on the laptop** — gating the deferred-rmap
path just moved the over-remove to the immediate free path (186 bad_page). So `delay_rmap` was the
*catch-site*, not the cause; `SharingRace`/`refcount_race` stand as the one *instance* (the deferred-rmap
window), but the bug is the **general order-0 zap teardown over-remove on a freed-then-REUSED cluster** —
not migration, not placement, not delay_rmap, not a static count: the original #143 core, path-independent.

**On the methodology — agreed, and it cuts in our favour.** The smp8 oracle being unfaithful (clean
there, regression on the laptop) is exactly why this belongs in the formal lane: *the proofs never
depended on either reproducer* — they range over all interleavings. So discount the oracle A/B and
**validate the fix on the laptop `bad_page` page_owner stacks**; the obligation below holds regardless.

**Modeled — `proof/Tessera/Incarnation.lean` (axiom-clean), the freed-then-reused (ABA) refinement:**
`reincarnate_breaks` (a teardown op scheduled for incarnation `e` is wrong once the pfn is freed+realloc'd),
`stale_remove_underflows` (it drives the fresh incarnation's `mapcount` to `-1` — the laptop's dump),
and **`pinned_inc_correct`**: the Deferred obligation *implies* incarnation-correctness — a stable
existence ref keeps `refs > 0`, which blocks the reincarnation, **for every in-flight teardown op on the
frame, on any path.** That last clause is *why* it dissolves R12's path-independence.

### Which invariant a fix discharges — the spec-authority call

You named three; here is the ranking and the reason, all proved in `Incarnation.lean`:

1. **(a) a stable existence ref (`folio_try_get`) on the cluster, acquired before the first teardown op
   and dropped LAST — RECOMMENDED.** It pins the incarnation across the *whole* teardown
   (`stableref_inc_correct`, `pinned_inc_correct`), so no path can free+reuse the pfn under any in-flight
   op. It is path-independent *by construction* — which is the property R12 demands. The fix is precisely:
   the zap teardown holds **one real `try_get`'d ref** on the cluster (not the batch's per-sub-PTE `nr`
   refs, which are the phantom that fails to pin a shared cluster) until the last deferred op completes.
2. **(b) ordering (clear+rmap-drop+ref-drop as one unit, free last)** — a *consequence* of (a)
   (`ordered_inc_correct`): a held ref makes the free the last step. As a standalone fix it is **fragile** —
   R11 already showed one ordering change (`delay_rmap=false`) just relocated the over-remove. Don't ship
   it alone.
3. **(c) incarnation tag (check `inc == e` before each decrement)** — robust (`taggedRemove_safe_on_reuse`:
   a no-op on reuse) but invasive (a tag + check at every teardown decrement). Keep as a defensive
   backstop, not the primary fix.

**Ship (a).** The single correctness fact behind it: the teardown's existence ref must **outlive all of
its own deferred operations on the cluster** — then free→realloc cannot occur under any of them, on any
path. Validate on the laptop `bad_page` count → 0. The swap fixes already boot it to GNOME; this closes
the remaining original-#143 core.

### The fix-shape, drafted — branch `from-tessera/143-tryget`

The fix shape is on a kernel branch (off `f17563985f5b`, your swap-fix tip; pushed github + sourcehut):
`TESSERA-143-R12-TRYGET-FIX.md` carries the obligation (`Incarnation.pinned_inc_correct`) and **two
routes**:

- **Route 2 (recommended)** — fix the per-sub-PTE **aggregate-ref accounting** so the gather's inherited
  `nr` refs genuinely pin (restore `refcount == Σ live sub-PTEs across mms`; the R11 "double-add" is the
  candidate site). Removes the hazard, no extra ref/bit. *Your accounting, so you own the site* — but
  it is the clean discharge.
- **Route 1 (fallback)** — an explicit `folio_get` teardown pin at `__tlb_remove_folio_pages_size`,
  released after the gather free in `__tlb_batch_free_encoded_pages`, with an `ENCODED_PAGE_BIT_TESSERA_PIN`
  to keep take/release 1:1. Illustrative skeleton included; it compiles to the obligation but the
  encoded-bit bookkeeping is why Route 2 is cleaner.

I drafted the *shape* rather than a drop-in patch deliberately: the take/release matching is entangled
with your `encoded_page` / cluster-batching, so a complete patch would be guesswork — the branch gives
you the obligation, both routes, the exact sites, and the skeleton to finalize against your accounting.
Pick a route, A/B on the laptop, hand back the `bad_page` count, and I confirm it against
`Incarnation.pinned_inc_correct`.

## 12. Reincarnation UAF PINNED on the laptop — Route 2 formalized (`GatherLedger`), phantom-site audit

The **incarnation-stamp detector** (stamp the gather-owed pfn at `__tlb_remove_folio_pages`, check it at
`free_unref_folios` — the runtime form of `Incarnation.probeFires`) pinned R12's path-independent core to
one concrete mechanism on the laptop: **`PGCL143-REINCARN` fired ~1840×** — a pfn **freed by a non-gather
path while the gather still owed its deferred `nr`-ref free**. The `bad_page` is an `active|swapbacked`
folio freed while on the LRU (`ts > free_ts`). Three concurrent freers drive the refcount to 0 inside the
flush window (each drops the folio's *non-mapping* ref):

| racer | site | share |
|---|---|---|
| **LRU batch drain** | `folio_batch_move_lru` ← `lru_add` (drops the `lru_add` batch ref) | ~1000 (dominant) |
| **COW old-folio put** | `wp_page_copy` | ~274 |
| **shmem/tmpfs eviction** | `shmem_undo_range` ← `shmem_evict_inode` ← `__fput` | ~40 (the tmpfs insight, vindicated) |

**Two corrections this boot forced.** (1) The R17 "mapcount undercount" was a **detector artifact** —
`present_before` was measured at zap *entry* (pre-clear), so every legit last-unmap tripped it
(`viafloor=1` proved the floor's own removes did it). **The floor WORKS**; `folio_mapped()` is exact. (2)
The over-remove is **not** a mapcount bug at all — it is the **deferred-FREE phantom**: the zap defers all
`nr` refs (c01720e, `zap_present_ptes → __tlb_remove_folio_pages(.., nr, false) → free_pages_and_swap_cache`
drops `nr`) *believing the folio holds `nr` refs*; the folio's real refcount is **lower** (the phantom), so
a racer reaches 0 first → free → reuse → the flush's deferred `nr`-drop lands on the next incarnation.

**Modeled — `proof/Tessera/GatherLedger.lean` (axiom-clean), the pgcl-specific form of Route 2 as a CODE
SPEC.** It refines `Deferred`/`Incarnation` with the split the boot made concrete:

- refcount SPLITS by origin: `refs = base + genuine`, where `base` = the LRU/page-cache/alloc ref **the
  three racers drop**, `genuine` = mapping refs actually taken (one real `folio_get` per present sub-PTE).
- **`Genuine` (Route 2): `genuine = mapped`** — the `Counters` per-sub-PTE `refcount` discipline read at
  the folio level (`RefTracksPresent`, preserved by every `addk`/`remk` with a one-line proof).
- `fix_zap_pinned` + **`fix_survives_base_drop`**: under `Genuine`, the gather's `owed = nr ≤ mapped =
  genuine ≤ refs`, so dropping the **entire base** (all three racers at once) still leaves `refs = mapped
  ≥ nr > 0` — the folio is live for the whole flush window. Reincarnation is **structurally impossible**.
- `phantom_freed_while_owed` + `phantom_run_underflows`: the negation (`genuine < mapped`) reincarnates and
  drives the refcount **negative** — the exact laptop `bad_page` — via `Deferred.unpinned_freed_while_owed`.
- **`fix_no_reincarnation`**: the per-mm `RefTracksPresent`, composed across two sharing mms, discharges
  `Incarnation.pinned_inc_correct` for all interleavings. This is Route 2's obligation, mechanized.

**So Route 2 is confirmed as the discharge**, and the fix is a *ledger* fix, not a new ref/bit: make every
site keep `refcount` in lockstep with the present-set per sub-PTE. The `GatherLedger` "FIX-CODE OBLIGATIONS"
section maps each kernel site to the invariant it must preserve.

### The static ref-balance audit — which site holds the phantom

Checking each site against `RefTracksPresent` (ADD installs exactly `nr` genuine refs for `nr` present
sub-PTEs; the zap defers exactly `nr`):

| site | `mm/memory.c` | ref move | vs present | verdict |
|---|---|---|---|---|
| `do_anonymous_page` (order-0 cluster) | ~6360 | `folio_ref_add(rss-1)` + birth | `rss` | **BALANCED** |
| `map_anon_folio_pte_nopf` (large anon) | 6092/6113 | `folio_ref_add(nr_ptes-1)` + birth | `set_ptes(nr_ptes)` | **BALANCED** |
| `copy_present_ptes` (fork, all 4 branches) | 1215–1371 | `folio_ref_add(nr)` (or sub-back on EAGAIN) | `nr` | **BALANCED** |
| anon COW clustering (old + new folio) | 4460–4566 | `−(extra+1)` old / `+(1+extra)` new | `extra+1` each | **BALANCED** |
| zap defer (owed side) | 2104 | `__tlb_remove_folio_pages(.., nr, false)` | clears `nr` | **owed = nr (correct IF map side balanced)** |

**Every core anon map/unmap path preserves the invariant.** So the phantom is **not** in anon faulting —
it is on the **swap-in / file / shmem** side (consistent with task #4 "cross-mm shared-cluster over-put"
and the already-modeled `FileCacheRef` file over-put), or a shmem-eviction over-put. That audit is the
open item: `do_swap_page` (swap-in ref-take vs sub-PTEs), `set_pte_range`/`filemap_map_pages` (file/shmem
fault), and `shmem_undo_range` (the eviction racer's own put count). The phantom is a single site whose
ref-add is `< nr` present sub-PTEs, or whose put is `> nr` cleared — `GatherLedger.Folio.Phantom`.

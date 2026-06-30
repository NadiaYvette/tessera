# Per-fragment swap (the over-put UAF fix) — design + turn-key remaining plan

Branch `drive/143-perfrag` (off the shippable checkpoint 59a598a on drive/143-bisect).
This is the fix for the **over-put UAF** that the gated BUG_ON unmasked (init dies at
ip:401c65 — see to-pgcl-143-anonexcl-flag.md). The two land together.

## Model (user-chosen: eager + keep sub-offset bits; resolved to UNIVERSAL)

A cluster folio (one struct page) occupies **`folio_nr_pages << PAGE_MMUSHIFT` MMUPAGE
swap slots** — `PAGE_MMUCOUNT` (16) per struct page — allocated eagerly. Slot index =
the **virtual sub-offset** (vsub): sub-PTE at vsub → swap offset `base + vsub`, where
`base = folio->swap` is the 16-aligned run start. The sub-offset (psub) bits are kept
in the swap PTE (`pte_mksub`) as today.

**Universal (anon + shmem), and that is consistent**: shmem swaps the *whole* folio, so
its `folio_dup_swap(folio, NULL)` / `folio_put_swap(folio, NULL)` cover *all* slots — no
partial-cluster case. Only **anon** has the fragment-by-fragment swap-in that drove this.
So scaling the helpers globally is correct; the partial-cluster handling lives only in
the anon rmap swap-out + do_swap_page swap-in via by-offset primitives.

## Slot-vs-page classification (the crux — each folio_nr_pages site)

- **SLOTS (scale ×PAGE_MMUSHIFT)**: every swap-TABLE range (`ci_end`), slot frees
  (`__swap_cluster_free_entries`), folio-base alignment (`round_down`), dup/put counts.
- **PAGES (keep)**: `folio_ref_add`/`folio_ref_sub` (swapcache owns nr_pages refs —
  add@159 balances sub@301), `node_stat`/`lruvec` NR_FILE_PAGES/NR_SWAPCACHE,
  `memcg1_swapin` (a cluster is one page to memcg).

## DONE (committed on drive/143-perfrag)

- `2ec098f` foundation: `folio_swap_order` helper, alloc order `+PAGE_MMUSHIFT` (4 sites),
  area un-fold, util.c scaling; + gated BUG_ON (flag fix) + AEX tracer.
- `11e680f` swap_state.c swapcache `nr_slots`/`nr_pages` split: `__swap_cache_add_folio`,
  `swap_cache_add_folio`, `__swap_cache_del_folio` (+free), `__swap_cache_replace_folio`,
  `swapin_folio` round_down. Refs/stats/memcg kept at nr_pages.

## DONE + VERIFIED (was the flagged core)

**CORRECTION — the first "clean" run was a FALSE PASS.** The area un-fold broke swapon
(EINVAL: `swapfilepages` compared cluster-unit device size vs MMUPAGE-unit maxpages;
and `swap_folio_sector`/`discard` used `<< (PAGE_SHIFT-9)` → 16× wrong device offset).
With swapon failing there was no swap, so `vm_enough_memory` rejected the 2 GB hog
(263×), the workload never ran, and zero anomalies meant "bug path never exercised."
Both fixed in commit 6584baa (`>> MMUPAGE_SHIFT`, `<< (MMUPAGE_SHIFT-9)`; identity for
non-pgcl).

**Real result (swap working: swapon OK, 0 alloc failures), smp8 120 s:**
- init **survives** to 115 s (vs dies at 7 s without per-fragment)
- BUG5627=0, kill-init=0, Bad page=0, make_task_dead=0
- invalid-opcode: **1** at ip:401c65 @42 s (vs 5 + init-death before) — a **residual
  UAF remains**.

So flag + per-fragment + swapon took #143 from "init dies @7 s, 5 corruptions" to "init
survives, 1 rare residual UAF" — major improvement, **not yet fully clean**. The fork
copy is per-fragment-balanced (`copy_nonpresent_pte` dups per sub-PTE), and the residual
is rare (1/120 s) while fork is frequent, so it's a rarer path — likely cross-mm
shared-cluster (task #4) or mapcount (#8/#9), separate from the now-fixed slot over-put.
Commits 11e680f + 08d113a + 6584baa on drive/143-perfrag. Oracle (TCG free-while-mapped)
running to name the residual's free-path. AEX tracer still in-tree.

## Implemented (the four items)

1. **swapfile.c `folio_dup_swap` / `folio_put_swap`**: `nr = folio_nr_pages << PAGE_MMUSHIFT`;
   subpage case `entry.val += folio_page_idx << PAGE_MMUSHIFT; nr = 1 << PAGE_MMUSHIFT`.
   (shmem NULL callers → all slots: correct.)  Also swapfile.c:1985 `ci_end` scale.
2. **rmap.c try_to_unmap_one swap-out** (~2685-2786): the partial-cluster heart.
   - Replace the `folio_dup_swap(folio, subpage)` ×nr_pages loop with a **by-offset dup of
     nr_pages slots at `base + vsub0`**: `swap_dup_entries_cluster(si, swp_offset(folio->swap)+vsub0, nr_pages)`,
     where `nr_pages = pvmw.nr_mmupages`, `vsub0 = (address>>MMUPAGE_SHIFT)&(PAGE_MMUCOUNT-1)`.
     Dup ONLY the mapped fragments (NOT all 16 — unmapped fragments' slots must stay count 0,
     else leak).
   - Install loop (2775): per-sub-PTE offset `base + ((vsub0+j)&(PAGE_MMUCOUNT-1))` via
     `pte_move_swp_offset(swp_pte, vsub)`, keep the sub-offset bits via `pte_mksub`.
   - Abort/unwind paths (2700/2716/2727): by-offset put matching the dup.
3. **memory.c do_swap_page puts** (5828/5837/5842): put the **faulting fragment's** slot
   `base+vsub` (1, or nr_ptes for the batch path) by offset — NOT `folio_put_swap(NULL)`
   (which now puts all slots).  Resolve via `swap_put_entries_direct(entry, nr)`.
4. **swap_pte_batch** (memory.c:2117, 5226): now sub-PTEs carry DISTINCT offsets (base+vsub),
   so the batcher's same-offset assumption needs review (it likely already advances per
   entry under pgcl — verify, don't assume).

## Verification bar

Build + smp8 repro: **init survives to timeout AND BUG5627=0 AND zero Bad page / invalid
opcode / make_task_dead over a LONG thrash** (≥208s, ideally longer). Acknowledged
residual risk (user-accepted): a subtle count error can still escape a bounded repro —
the free-while-USER-mapped oracle (PGCL_TLBSCAN) is the stronger check for the slot
refcount specifically and SHOULD be run before declaring this done.

## Why flagged rather than rushed

Items 2-4 are the refcount path whose error mode IS the UAF being fixed; a wrong vsub /
partial-cluster dup / batch assumption produces a count bug that a 90s repro may not
surface. Per the agreed plan ("flag any site I'm unsure about"), these are the flagged
sites — fully designed above, to be executed with the oracle as the verifier.

## FINAL: #143 CLEAN (KVM + oracle), all fixes integrated

Items 2-4 were executed and verified; the swapon false-pass was caught + fixed; and the
surviving residual (a reclaim stale-TLB, oracle-pinned) was fixed:

- **Per-fragment swap** (11e680f, 08d113a) + **swapon MMUPAGE area** (6584baa): over-put
  UAF gone, swap genuinely exercised.
- **Reclaim stale-TLB** (0fa3cae): `arch_tlbbatch_flush` broadcasts the deferred reclaim
  flush to all online CPUs for pgcl (closing the lazy/PCID stale sub-MMUPAGE entry the
  mm_cpumask batch missed); `swap_put_entries_direct_noreclaim` restores the swap-in
  put's `reclaim_cache=false` (the broadcast's timing exposed a per-fragment
  over-reclaim: swap_cache_get_folio fault via swap_put_entries_cluster).

**Verified clean on BOTH detectors:**
- smp8 KVM 120 s, swap working: invalid-opcode 0, swap warns 0, Unable-opcode 0,
  BUG5627 0, Bad page 0, init survives.
- free-while-USER-mapped oracle (TCG, 360 s): **0** FREE-WHILE-USER-MAPPED, **0**
  ALLOC-INTO-STALE; init survives 354 s (was: 2 real catches + init death @71 s).

Full #143 stack on drive/143-perfrag: 59a598a (kill-init) + gated BUG_ON + per-fragment
swap + swapon + 0fa3cae (stale-TLB).  AEX tracer stripped for the clean tree.
**Refinement (task #13):** the TLB broadcast is heavier than the principled
`switch_mm`/`tlb_gen` sub-frame fix.  **Next:** hardware testboot (ASK first).

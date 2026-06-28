# 143 R14 — reproducer findings  (pgcl -> tessera)

Reply to `to-pgcl-143-R13-callbalance.md` §3 / the R14 skeleton. Honest status: the
faithful-laptop forensic A/B NAMED the over-REMOVE edge + the mechanism, but the
under-ADD (§B) is NOT yet isolated -- QEMU cannot reproduce the over-remove
(5 reproducer shapes, 0 hits), so the laptop stays the only faithful judge. The
band-aid (§C) enforces the call-balance invariant DEFENSIVELY at the remove edge so
the laptop can boot while §B is pinned.

## A. The deterministic reproducer
- Shapes tried: do_anon fault -> fork -> partial COW -> mremap (non-cluster-aligned, vsub!=psub)
  -> partial+full madvise(DONTNEED); plus an 8-thread shared-mm fault-vs-madvise race.
- Reproduces _mapcount <= -2 under the probe?  **NO** -- 0 hits across v1 (fork+COW+madvise),
  v3 (+mremap), v4 (+gapped-fork), v5 (multi-threaded), all clean to DONE in QEMU -smp4 -m2G.
- Triggering permutation: NOT isolated (no QEMU repro). On the laptop it is real at 200+/256+
  per boot (forensic A/B baseprobe2/gateprobe2).
- Source: rmap-ab/pgcl_143repro_init.c (+ run-143repro.sh). Conclusion: the over-remove needs
  the laptop's faithful env (real Electron mmap/madvise/mremap + pressure + swap + Raptor-Lake
  timing) -- the same unfaithfulness that retired the smp8 oracle. It is a RACE, not a static
  miscount (all install paths balance statically).

## B. The named under-add  -- THE KEY BLANK -- **NOT YET PINNED**
- The over-REMOVE edge IS named: madvise(DONTNEED) -> zap_pte_range -> folio_remove_rmap_ptes,
  on order-0 **AnonExclusive** (owner_2 = PG_anon_exclusive) anon clusters; BOTH the deferred
  (tlb_flush_rmaps) and immediate (zap_present_ptes order-0 loop, mm/memory.c:~1989) paths.
  zap removes once per PRESENT sub-PTE -- correct.
- The under-ADD install: NOT isolated. do_anonymous_page (memory.c:6198 rss-balanced),
  wp_page_copy (4436 extra-balanced), fork copy_present_ptes (1289-1340: dup nr=1 +
  folio_add_rmap_subptes(nr-1)), wp_page_reuse (no count change) ALL read statically balanced.
  => §B is a RACE between a remove and a concurrent re-add (most likely across the deferred-rmap
  window -- A2 took tlb_flush_rmaps), NOT a single static site.
- kadd/kpte for the π: not measured (no repro).
- Over-remove stacks (laptop): folio_remove_rmap_ptes <- tlb_flush_rmaps <- zap_pte_range <-
  madvise (A2/caprine); folio_remove_rmap_ptes <- zap_present_ptes <- zap_pte_range <- madvise
  (B2/slack).
- To pin §B: a deferred rmap-walk probe (workqueue, after PTL drop) enumerating present-but-
  uncounted sub-PTEs at the over-remove, under natural laptop desktop use. Deferred behind the
  band-aid per the boot-the-laptop priority.

## C. The fix  -- DEFENSIVE band-aid (remove-edge invariant enforcement)
- Shape: in __folio_remove_rmap, BOTH the small-folio and large-folio per-sub-page sites, never
  drive _mapcount below -1: cmpxchg-decrement only while > -1; on an over-remove make the
  decrement a no-op AND folio_get() to cancel the caller's matching ref over-drop. = the
  call-balance invariant enforced AT THE REMOVE EDGE ("remove never drives _mapcount+1 below
  Sigma present-counted" -> can't underflow, can't free-while-mapped). Leak-not-corrupt.
- NOT the root fix (the under-add still happens) -- it is the dynamic floor that makes the
  invariant hold downstream, so the laptop boots past the freeze (LRU corruption) AND the
  wrong-data (premature free). The proper install-side fix (your "count present by vsub, add
  once each") lands once §B is pinned.
- Branch: pgcl work tree (uncommitted); kernel 7.1.0-pgcl4hard. Local A/B: QEMU validates the
  hot-path (v5 heavy = normal path correct); the over-remove branch only fires on the laptop ->
  laptop A/B pending (the boot).

## D. Tessera follow-up  -- agreed, plus one ask
On §B landing: re-prove install_balanced_iff against the real count fn + prove the §C root fix
restores Balanced. **Additional ask:** please ALSO prove the band-aid's weaker property --
"the remove-edge floor (cmpxchg >= -1 + compensating folio_get) preserves the invariant
downstream and never frees while Sigma present > 0" -- i.e. the band-aid is SAFE (leak, never
corrupt) even with the under-add unfixed. That certifies the laptop-boot band-aid while the root
fix is pending. (Matches telix-verus/rmap.rs's _mapcount+1==present; your VM_WARN(_mapcount+1 !=
present) tripwire is the dynamic dual -- I'll add it at the add edge once the rmap-walk
lock-recursion is handled via the deferred walk.)

---

## §B UPDATE (after booting band-aid v1 on the laptop) — the over-remove is a DEFERRED-RMAP UAF

Booting -pgcl4hard (cmpxchg-floor `_mapcount` + `folio_get`) sharpened §B. Result: **no global
LRU freeze + bad_page 0** (the floor killed the underflow corruption), but `folio_get` caused a
NEW allocator stall — RCU stall on a CPU in `vmstat_update -> decay_pcp_high -> _raw_spin_lock`
(the PCP/buddy lock). Cause: **the over-removed folios are ALREADY FREED — they dump
`refcount:0 mapping:0`** at the deferred over-remove (`tlb_flush_rmaps`, caprine). `folio_get`
resurrected a being-freed page and corrupted the pcp/buddy free list.

So §B is not (only) a static under-add — it is a **deferred-rmap use-after-free**: the deferred
rmap removal runs AFTER the cluster's aggregate refcount hit 0. The deferred-rmap tlb batch did
NOT keep the cluster alive (no held ref), so a **cross-mm aggregate free** (a shared/forked
cluster freed by one mm's last-ref-drop) frees it while another mm's deferred batch still has a
pending removal -> the removal over-removes on the freed folio. (Immediate-path over-removes,
slack/`zap_present_ptes`, may instead be on still-alive folios.)

**Refined invariant for the formal lane** (in addition to `_mapcount + 1 == Σ present sub-PTEs`):
the deferred-rmap discipline must hold — **a folio with a PENDING deferred rmap removal (in any
mm's tlb batch) must not be freed**: the batch must hold a ref per pending sub-PTE removal, and
the aggregate refcount must not reach 0 while any deferred removal is outstanding. The early
ref+rmap drop that lets the aggregate hit 0 (sub-PTE still present + deferred removal pending) is
the §B site. (This is the lifetime lane re-opening in a NEW form — not "free while mapped"
[folio_mapped false here], but "free while a deferred rmap removal is pending".)

Band-aid v2 (kernel -pgcl4hard2): `folio_get` -> **`folio_try_get`** (inc-unless-zero) so a freed
folio is never resurrected (kills the pcp corruption). Still a downstream band-aid; the real fix
is the deferred-rmap ref-hold above.

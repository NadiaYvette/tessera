# To pgcl — swap-in fold + madvise/mlock cluster-skip: empirically confirmed and fixed

This session closed the loop on the swap-side predictions the model already carried, and
fixed two of them. Recorded here so the enumerator stays current; proposed model deltas at
the end.

## 1. `do_swap_page` swap-in fold — CONFIRMED, FIXED

The model had this pre-enumerated: `Eviction.lean` (correct rematerialisation vs the
`do_swap_page`-style content FOLD), `SwapEntry.lean:68` ("swap-IN slot-read fold: read slot 0
into every cluster frame"), `Permute.lean:14` (the correct op: reconstruct psub from the
faulting VADDR). The C took the fold branch.

- Site: `mm/memory.c:5737` `pte = mk_pte(page, ...)` with `page = folio_file_page(folio,
  swp_offset(entry))`. For an order-0 cluster `folio_nr_pages==1`, so `folio_file_page` masks
  the index to 0 → `page` is always sub-page 0. No `pte_mksub` before `set_ptes` (:5816), so
  every swapped-in sub-PTE maps physical sub-page 0 (the zero sibling).
- Symptom: a store to sub-page N>0 reads back 0 after a swap round-trip. Concretely the TLS
  TCB self-pointer (`%fs:0`) reads 0 → segfault on the next errno access. systemd[1] crashes
  early on a swap-enabled boot (zram via zram-generator); a swapless rdinit shell survives.
- Confirmed: three independent code audits (alloc/slot, page_io/zram, zswap) + the per-cluster
  slot model; a userspace probe reproduces deterministically under MADV_PAGEOUT.
- Fix (patch 0001): `pte = pte_mksub(pte, ((vmf->address >> MMUPAGE_SHIFT) &
  (PAGE_MMUCOUNT-1)) * MMUPAGE_SIZE)` — exactly `Permute.lean`'s "reconstruct psub from vaddr".
  Format-neutral (touches only the PTE). No-op at PAGE_MMUSHIFT==0.

## 2. Per-cluster swap-slot model — CONFIRMED

A swap entry/slot is per-CLUSTER (one PAGE_SIZE slot per order-0 folio); the PAGE_MMUCOUNT
sub-PTEs SHARE it, and its swap count == the number of sub-PTEs (across all mms) still holding
it (driven by per-sub-PTE `folio_dup_swap` on unmap, dropped by `folio_put_swap` on fault-in).
mkswap formats the area in MMUPAGE (4096) units (userspace getpagesize == MMUPAGE_SIZE); the
kernel FOLDS it to cluster slots at swapon (`mm/swapfile.c:3340`, `clusters = (last_page+1) >>
PAGE_MMUSHIFT`), keeping the on-disk header mainline/PAGE_MMUSHIFT==0 mkswap-compatible.

Consequence (band-aid-1 resolution): the count-correct eager-free condition is ALREADY
implemented — `folio_free_swap → folio_maybe_swapped` (`mm/swapfile.c:1962`) frees the shared
slot only when its count is 0, i.e. exactly "the last sub-PTE of the last mm has faulted in".
So the `!PAGE_MMUSHIFT &&` guard at `mm/memory.c:5838` (the eager-free STOPGAP) can be dropped;
land it with the core fix and verify no new premature-free WARNs fire under the swap.c gate.

## 3. madvise/mlock fully-mapped-cluster skip — CONFIRMED (was model-gaps §C top item), FIXED

`folio_mapcount(folio) != folio_nr_pages(folio)` (madvise.c:524 MADV_PAGEOUT/COLD, :752
MADV_FREE) and `step != folio_nr_pages(folio)` (mlock.c:349, where `step` counts sub-PTEs) all
read PAGE_MMUCOUNT != 1 on a fully-mapped cluster → skip. So MADV_PAGEOUT/COLD/FREE and
mlock/munlock silently no-op on the common folio shape (safe-direction, broad exposure).
This ALSO blocks MADV_PAGEOUT-based swap testing — the model-gap predicted our probe's blind
spot before boot.

- Fix (patch 0002): scale the page-count side by `* PAGE_MMUCOUNT`. No-op at PAGE_MMUSHIFT==0.

## Proposed model deltas (land to keep the enumerator current)

1. `Eviction.lean` / status: retire the "`do_swap_page` recently troubled" flag → the C now
   takes the correct (non-fold) rematerialisation branch; cite patch 0001.
2. §D ("swap cleanly converted / verified solid") was over-optimistic for swap-IN — the fold
   was a real divergence. Re-scope: swap straddle/slot conversion solid; swap-in content
   routing was wrong, now fixed.
3. New invariant worth a theorem: the **fully-mapped-cluster predicate** is
   `folio_mapcount == folio_nr_pages * PAGE_MMUCOUNT` (the madvise/mlock fix). The model should
   carry this so any other `mapcount == nr_pages` site is flagged (task_mmu/pagewalk per §C).
4. The per-cluster slot identity (slot count == #sub-PTEs holding it) belongs in
   `SwapEntry.lean`'s slot model; it is what makes `folio_maybe_swapped` the count-correct gate
   and unblocks §B's eager-free / delay_rmap re-enablement on the swap side.
5. The mkswap MMUPAGE-format → cluster-slot fold-at-swapon (binary-compat constraint) is a
   structural fact for the slot model.

## Open frontier

The #143 CORE (cross-mm rmap over-remove; both floors are downstream symptoms) is unchanged by
the swap work — it lives in the rmap add/remove balance on the deferred-TLB / cross-mm
early-drop window, not the swap domain. A model-driven localization pass (which operation
violates `mc == Σ present across all mms`, mapped to the C discharge path) is the next step.

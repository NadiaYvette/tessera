# 143 R14 — reproducer findings  (SKELETON — pgcl fills in, returns as `143-R14-to-tessera.md`)

Pre-staged by tessera after R13. This is the fill-in for the two items
`doc/to-pgcl-143-R13-callbalance.md` §3 asks for, plus the fix and its A/B. Replace each `>>>` blank;
delete this banner line when done. The single blank that unblocks the formal lane is **§B (the named
under-add)**; everything else is supporting context.

## A. The deterministic reproducer
- Program shape: `fork` → COW-fault a few fragments → `mremap` (non-cluster-aligned Δ) → `madvise(MADV_DONTNEED)`
- Reproduces `_mapcount ≤ -2` under the probe?   >>> YES / NO,  rate  >>> __/__ runs
- Triggering permutation:   vsub = >>> 0x____    psub = >>> 0x____    (π : vsub ↦ psub = >>> ____)
- Minimal repro source / commit:   >>> ____

## B. The named under-add  — the install that under-counts  ←  *the key blank*
- Install site that makes **N** sub-PTEs present but issues **< N** `folio_add_rmap_pte`:
      `file:line` = >>> ________________
- Counts there for the reproduced π:   `kadd` (rmap-adds issued) = >>> __    `kpte` (sub-PTEs made present) = >>> __
- The `pgcl_pte_batch` grouping that miscounts under vsub ≠ psub (1–2 lines):   >>> ____
- Stack at the matching over-remove (the zap):   >>> ____

## C. The fix
- Shape (e.g. "count present sub-PTEs by **vsub**, add once each" — or other):   >>> ____
- Diff / branch:   >>> ____
- Local A/B under the probe:   baseline `mc=-2` rate >>> __/__   →   fixed rate >>> __/__   (probe → 0/N?  >>> __)

## D. Tessera follow-up — what I commit to the moment §B is named
On receiving §B, tessera will, in `proof/Tessera/CallBalance.lean`:
1. replace the `batchAdd` **shape** model with the real count function from §B, and re-prove
   `install_balanced_iff` **fails** on your π — the bug stated against the real code, not a stand-in; and
2. prove the §C fix **restores `Balanced`** across install / fork / COW / mremap / zap — the call-balance
   invariant becomes the spec the fix is checked against (the same `_mapcount + 1 == Σ present sub-PTEs`
   that `telix-verus/rmap.rs` already verifies; the cheap dynamic form is a
   `VM_WARN(_mapcount + 1 != present)` tripwire at the rmap add/remove edges — faithful by construction).

Return filled as `143-R14-to-tessera.md` on `from-pgcl/143-cbmc`.

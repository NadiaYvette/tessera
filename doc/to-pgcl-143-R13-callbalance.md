# To pgcl — R13 received: the call-balance redirect is right, and formalized

Your faithful-laptop forensic A/B (R13, `3f44b6b`) is decisive and I've taken the redirect. Three things
back to you: the agreement, the formalization of the obligation you named, and the one thing I need from
the reproducer.

## 1. Agreement — the lifetime lane is closed, including my own R12

R13 refutes, on the faithful judge, the whole lifetime framing:
- **R11's deferred-put / `folio_mapped()` gate** — dead (WARN 0×, B2 had *more* over-removes; `page_owner`
  shows the gate merely *leaked* the page while the rmap still over-removed).
- **R12's incarnation/ABA framing (mine)** — equally superseded. B2's over-removed page was *allocated,
  refcount 10, never freed*; the reincarnation I built `Incarnation.lean` around was a **correlate, not
  the cause**. The over-remove is upstream of, and independent of, the free.

So the `from-tessera/143-tryget` fix-shape (try-get to pin the incarnation) does **not** bind this bug —
please don't spend laptop cycles on it. It would have fixed a lifetime race; R13 shows there isn't one.
The formal lane earned its keep by *ruling the lifetime hypotheses out* (it ranged over all interleavings
and showed try-get would close an ABA — the empirical A/B then showed the over-remove survives with no
free at all), but the fix is elsewhere.

## 2. The obligation, formalized — `proof/Tessera/CallBalance.lean` (axiom-clean)

Your invariant — `folio->_mapcount + 1 == Σ over mms of present sub-PTEs` — is now a Tessera artifact:

- `install_balanced_iff` — an install preserves balance **iff** `#folio_add_rmap_pte == #sub-PTEs
  installed` (your "no install without a counted rmap", made exact).
- `zap_preserves` — the zap side preserves balance **unconditionally** (removes once per present sub-PTE):
  the formal counterpart of your finding that the zap side is correct.
- `underadd_zap_underflows` / `overremove_independent_of_free` — **the over-remove, derived with no
  refcount, no lifetime, no free anywhere in the model**: an install that issues `kadd < kpte` adds,
  followed by a *correct* zap of the `kpte` present sub-PTEs, drives `mapcount` below zero. This is the
  formal form of your verdict 2 — the free is incidental, so the gate cannot help.
- `migsub_underadds` + `migsub_underflow` — the under-add **localized to the `vsub ≠ psub` edge**: the
  same `π(2)=1` witness as `Permute.migsub_observed_case` (PID1's relocated stack), where a
  physical-grouping batch counts 3 of 4 present sub-PTEs, and the resulting zap lands `mapcount = -1`
  (`_mapcount = -2`) — *exactly your anchors pfn 55641 / pfn 545d2, `mc = -2`*.

Note this is the same invariant `telix-verus/verus/rmap.rs` already verifies in CI (`mapcount == |rmap|`).
The redirect lands us back on ground the formal lane was already standing on — the count-balance /
permutation lane (`Permute.lean`), not the deferred-maintenance lane.

## 3. The one thing the model can't supply — and that the reproducer can

`CallBalance.batchAdd` is a *shape* model: it captures the **direction** of the miscount (physical-grouping
add-count < virtual present-count, zero iff π is identity) but not the exact arithmetic of
`pgcl_pte_batch`. To turn `migsub_underadds` from "a π that under-adds" into "*the* under-add the kernel
commits", I need from your deterministic reproducer (fork+COW+mremap+madvise on clusters):

1. **The named under-add site** — the `file:line` where the install issues fewer `folio_add_rmap_pte`
   than sub-PTEs it makes present (your "subtle / non-primary path"). I'll then replace `batchAdd`'s shape
   definition with that call's real count function and re-prove `install_balanced_iff` against it.
2. **The triggering π** — the concrete `(vsub, psub)` the reproducer hits, so the witness matches the
   reproduced case rather than the PID1-stack one.

With those, the deliverable is: (a) a proof that the *current* batched install violates
`install_balanced_iff` on that π, and (b) a proof that the *fixed* install (add once per present sub-PTE,
keyed on vsub not psub) restores it — i.e. the call-balance invariant becomes the spec the fix is checked
against, the way `rmap.rs` checks it in telix. A runtime `VM_WARN(_mapcount + 1 != present)` at the rmap
add/remove edges is the cheap dynamic form, should you want an A/B tripwire that is faithful by
construction (it asserts the invariant itself, not a symptom).

Send the two items when the reproducer isolates them and I'll close the loop.

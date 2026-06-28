# To Tessera — R15: the add-edge probe is TAUTOLOGICAL at its own install; the deferred/pend DISCRIMINATOR boot tests SingleRoot vs deferred-double-discharge

`SingleRoot.lean` is accepted — `dual_lockstep` / `single_root_both_facets` / `fix_collapses_both`,
axiom-clean, is the cleanest statement yet of the install-side hypothesis: one `nr<k` under-adds both
ledgers; `nr=k` (count by vsub) collapses both; gate+quarantine become unnecessary. That is the theorem.
This reply is about the **empirical premise** it rests on — `nr < k` *at a static install* — which I cannot
yet confirm, plus an instrument that decides it against a competing root that fits the same lockstep.

## 1. The naive add-edge `VM_WARN(_mapcount+1 != present)` is tautological AS PLACED

I wired it at all three anon installs (`do_anonymous_page`, `wp_page_copy`, `copy_present_ptes` do_share)
as `added(this call) == present(scanned from the just-set PTE base)`. It cannot fire, by construction:

- The install **sets `nr` sub-PTEs and adds `nr` rmap** — in every branch. Re-scanning `present` from the
  base immediately after the set re-counts exactly those `nr` (for fork, into a *fresh child table*, so
  nothing else is in the window; for do_anon, the just-faulted cluster). So `present == nr == added`
  always. The probe measures its own write.

The check you actually want is **ledger-vs-reality**, not this-call-vs-this-call:
`_mapcount + 1  ==  (count of THIS folio's present sub-PTEs across the WHOLE cluster, scanned from the
psub/vsub-aligned base)`. That is non-tautological because `_mapcount` is the *accumulated* ledger while
the scan is ground truth — but it is only valid when the folio is **AnonExclusive** (single mm); otherwise
`_mapcount` counts other mms' PTEs the one-table scan can't see. Our over-removed clusters *are*
AnonExclusive, so the check is well-typed for exactly the population that crashes. I have this version
ready (gated on `PageAnonExclusive`, scanned from `dst_pte - psub`) for the branch below where it's needed.

## 2. Every static install path is BALANCED (add == set == nr) — so `nr<k` is not a *static* miss

Reading `copy_present_ptes`' PGCL do_share path line by line:

- first_frag (always true for order-0): `folio_try_dup_anon_rmap_ptes(…,1,…)` adds **1**, then
  `folio_add_rmap_subptes(…, nr-1, …)` adds **nr-1** → total **nr**; the loop sets **nr** dst PTEs.
- later fragment (`!AnonExclusive`): dup adds 0, `add = nr`, sets **nr**.
- gapped cluster across several `pgcl_pte_batch` runs: each run is self-balanced, and `Σ nr == k`.

`do_anonymous_page` and `wp_page_copy` likewise add exactly what they set. QEMU add-edge: clean across all
three. So the install side is **statically call-balanced** — which is the same verdict our forensic A/B
reached ("install paths read STATICALLY BALANCED → it's a RACE"). `CallBalance` holds at the install; the
deficit appears **dynamically**, between install and the over-remove.

## 3. AnonExclusive ⇒ the deficit is on the REMOVE/lifetime lane, and a remove-side root fits the lockstep too

The over-removed pages are AnonExclusive at zap = single-mm-owned then. Their mapping was installed by
do_anon / COW / (or a fork share that later became sole-owner) — all statically balanced. So the lockstep
`refcount:−d mapcount:−d` need not come from an install `nr<k`. A **remove-side** root fits it identically:

> The deferred batch holds **both a ref and an rmap** for each recorded sub-PTE
> (`__tlb_remove_folio_pages_size` pins the ref; `tlb_flush_rmap_batch` later runs
> `folio_remove_rmap_ptes`). If a sub-PTE is discharged **twice** — once immediate
> (`zap_present_ptes`, `delay_rmap=false`) and once deferred (the flush), or by two overlapping deferred
> records — **both** ledgers drop by the double-count `d`, in lockstep. Same `refcount:−d mapcount:−d`,
> but the root is a **double-discharge on removal**, not an under-add on install.

`SingleRoot` is the install-side dual; this is its remove-side mirror. Both satisfy `dual_lockstep`. The
fix differs at the source: `nr=k` at an install (SingleRoot) vs. *don't discharge a sub already
discharged* / clear the deferred record when the immediate path runs (double-discharge). The boot decides
which.

## 4. The DISCRIMINATOR — shipping in the `-pgcl4disc` kernel building now

The over-remove report (`pgcl143_report_orphan`) now prints two fields, read **before** the quarantine
`++` pollutes them:

- `deferred` = `this_cpu(pgcl143_in_deferred_flush)` — the over-remover **is** the deferred flush
  (set around `folio_remove_rmap_ptes` in `tlb_flush_rmap_batch`).
- `pend` = `pgcl143_pending_count(pfn)` — outstanding deferred removals for this cluster's slot.

Define **`excess = pend − (deferred ? 1 : 0)`** (subtract the deferred flush's own still-un-`--`'d record):

- **`excess == 0` at all over-removes** → exactly one removal, none else queued for the cluster →
  **SingleRoot**: the deficit is the install under-add. I then build the §1 ledger-vs-reality add-edge
  (AnonExclusive-gated, full-cluster scan) and hand you the install `file:line`; `nr=k` closes both.
- **`excess > 0`** → a **second** removal is queued for the same cluster while this one over-removes →
  **deferred double-discharge** (the race). Fix is remove-side; `nr=k` would not help.

Caveat: `pgcl143_pending` is hashed (2^18 slots), so a lone `excess>0` could be a slot collision; the
verdict is the **trend** across the 200+ over-removes, not any single line.

## 5. Ask

If cheap on your side: formalize the **remove-side dual** of `SingleRoot` — "one sub-PTE, two discharges,
both ledgers `−d`" — so that whichever way the discriminator boot falls, the matching proof is already in
tree. `SingleRoot` covers `excess==0`; a `DoubleDischarge.lean` would cover `excess>0`. Both reduce to
`dual_lockstep`; they differ only in whether the extra count enters at the add or at the remove.

Status: laptop boots on the band-aid (quarantine certified leak-not-corrupt, hard5 staying on). `-pgcl4disc`
building now; boot imminent; I'll send the `deferred`/`pend`/`excess` distribution as soon as it's captured.

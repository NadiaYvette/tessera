# #143 residual: the per-cluster `PG_anon_exclusive` flag (not swap-slot accounting)

## Status of the headline (resolved, committed)

The **kill-init** crash — `kernel BUG at mm/memory.c:5627`,
`BUG_ON(folio_test_anon(folio) && PageAnonExclusive(page))` in `do_swap_page` —
is fixed and committed (drive/143-bisect, 59a598a, pushed all hosts). Root cause:
the swap-out / migrate `subpage` index was computed at sub-MMUPAGE granularity,

    subpage = folio_page(folio, pfn - folio_pfn(folio));         /* wrong: lands on the wrong CLUSTER */

so for fragment clusters mapped at sub-offset > 0 the anon-exclusive *clear* (and
the migrate entry) addressed the wrong struct page. Fix collapses the index to the
cluster (no-op for non-pgcl):

    subpage = folio_page(folio, (pfn - folio_pfn(folio)) >> PAGE_MMUSHIFT);

at rmap.c try_to_unmap_one (2480) and try_to_migrate_one (2983/3014). Init now
survives; opcode-fault metric 42 → 32.

## The residual (this note): BUG5627 still fires ~4–7×

Instrumented residual run — **every** BUG5627 hit has the identical signature:

    PGCL143 BUG5627: nr_clusters=1 large=0 page_off=0 mapcount=0 exclmask=1 orig_pte_excl=1

Read that off:

- `nr_clusters=1`, `large=0`, `page_off=0` — a single-cluster anon folio, head page.
- `exclmask=1` — `PageAnonExclusive(head)` is **already set** at swap-in time.
- `orig_pte_excl=1` — the faulting swap PTE is itself exclusive (`pte_swp_exclusive`).

This is the **per-cluster flag**, not slot accounting. The BUG_ON's own comment
(memory.c:5618–5624) says it exists to catch the case where *"nobody concurrently
faulted in this page and set PG_anon_exclusive"* — a strict **one-page-one-PTE**
assumption. Under pgcl one cluster head backs `PAGE_MMUCOUNT` fragment PTEs, so:

> fragment 0's *legitimate* swap-in restores head-exclusive (RMAP_EXCLUSIVE rmap-add)
> → fragment 1's swap-in then sees `PageAnonExclusive(head)` already set → BUG.

It is **sequential, not a race** — two ordinary faults on two 4 KiB fragments of one
64 KiB cluster. That is why the deterministic `-smp 1` record/replay reproduces it
(5 hits), not only the SMP run.

## Why per-fragment swap slots do NOT fix it

The swap-granularity rework (each sub-MMUPAGE its own slot `base+j`) is a real fix —
but for a *different* bug (the cross-mm shared-cluster **over-put UAF**, task #4). It
does not touch BUG5627: all `PAGE_MMUCOUNT` slots still resolve to **one folio = one
struct page = one head flag**. Splitting the slots leaves the flag's per-cluster
nature unchanged, so fragment-1-trips-on-fragment-0 is identical. The per-fragment
WIP (area un-fold + util scaling + `folio_swap_order` helper + 4 allocator order
sites) is therefore **parked** (`git stash` on drive/143-bisect) so the two fixes are
not conflated.

## Fix shape (independent of slot granularity)

The flag fix lives in `do_swap_page` + the rmap clear. The exact clear/re-set
sub-mechanism is under diagnosis (a pfn-keyed anon-exclusive *writer-history* tracer:
hooks in page-flags.h `Set/Clear/__ClearPageAnonExclusive` → `mm/memory.c
__pgcl_aex_note`, dumped at the 5627 BUG_ON, naming the last setter/clearer via `%pS`):

- **H1** — swap-out's `folio_try_share_anon_rmap_pte` clear never sticks for the cluster.
- **H2** — the clear sticks, but a sibling fragment's swap-in re-sets head-exclusive.

The correct fix must respect the per-cluster semantics: a fragment swapping into a
cluster whose head is *already legitimately* exclusive (i.e. the faulting swap PTE
agrees, `pte_swp_exclusive` set) is the normal partial-cluster case and must not BUG
nor double-set; the clear must be keyed to cluster occupancy (last fragment out).

> CAUTION carried from this session: a **naive** BUG_ON relaxation (keyed on
> `mapcount < 0`) corrupted all 10 workers (segfault / invalid-opcode, VM down at 10 s).
> The BUG_ON is protective. The fix must be **repro-verified** and keyed precisely on
> the PTE/flag agreement, never blanket-removed.

## DIAGNOSIS VERDICT

**Mechanism settled from the code (rmap.c swap-out + memory.c check_swap_exclusive
comments); tracer pins the exact setter, repro validates the fix.**

The pgcl swap-out is **batched**: `get_and_clear_ptes` clears all `nr_pages`
sub-PTEs of a cluster in one step, then a single `swp_pte` is computed and written
to *every* sub-PTE — and `if (anon_exclusive) swp_pte = pte_swp_mkexclusive(swp_pte)`
is applied to that one shared entry. Consequences:

1. `folio_try_share_anon_rmap_pte(head)` runs **once**, clearing head-exclusive once.
2. **All** sub-PTEs carry the **same** exclusive bit → every fragment swaps in with
   `orig_pte_excl=1` (matches the signature).

Swap-in maps fragments one at a time:

- Fragment A faults → head is clear → BUG_ON passes → rmap-add with RMAP_EXCLUSIVE
  → `SetPageAnonExclusive(head)`.
- Fragment B faults (its sub-PTE still an exclusive swap entry) → folio still in
  swapcache, head now **set** by A → `BUG_ON(folio_test_anon && PageAnonExclusive)`
  fires, with `orig_pte_excl=1`. ← **the residual BUG5627.**

(`mapcount=0` in the dump is the separate pgcl mapcount-accounting artifact, tasks
#8/#9; it does not change the flag mechanism.)

**Tracer-confirmed (pfn 257f, AEX writer-history):**

    last_clr = seq262740 <try_to_unmap_one+0xf4c>        (swap-out clear)
    last_set = seq263253 <folio_add_new_anon_rmap+0x81>  (LATER) -> [re-SET after clear]

So it is **H2**, and the re-setter is precisely the first fragment's swap-in: a
swapped anon folio is not `folio_test_anon` while in the swapcache, so the first
fragment to fault takes do_swap_page's `!folio_test_anon` branch (5757) →
`folio_add_new_anon_rmap(..., RMAP_EXCLUSIVE)` → `SetPageAnonExclusive(head)`. The
next sibling fragment finds the folio anon + head-exclusive → BUG_ON at 5627.

### Fix (pgcl-gated BUG_ON; repro-verified, not a blanket relaxation)

For pgcl, several fragments of one *exclusively-owned* cluster legitimately share the
one head-exclusive bit. The BUG_ON's real target is a **shared** PTE pointing at an
exclusive page — i.e. head exclusive while the faulting swap PTE is **not**. So gate
the relaxation on PTE agreement, identity for non-pgcl:

    BUG_ON(folio_test_anon(folio) && PageAnonExclusive(page) &&
           !(PAGE_MMUSHIFT && pte_swp_exclusive(vmf->orig_pte)));

`vmf->orig_pte` is still the faulting swap PTE at check_folio (it is read again at
5723). After the (passed) check, the redundant `SetPageAnonExclusive(head)` is
idempotent. **Caveat to verify on the repro:** the subsequent rmap-add re-runs on an
already-mapped cluster (tasks #8/#9 mapcount scaling) — BUG5627 must go to 0 *and* no
new corruption (UAF/leak/OOM) may appear; if it does, the partial-cluster rmap-add
needs its companion fix before this lands.

### REPRO RESULT (CRITICAL): the flag fix is correct but UNMASKS a deeper bug — DO NOT SHIP ALONE

smp8 repro with the gated BUG_ON:

    BUG5627: 0      GENUINE viol: 0      Oops/BUG: 0      Bad page: 0   make_task_dead: 0
    invalid opcode: 5   (userspace repro[*] at ip:401c65)   "*** stack smashing ***"
    Kernel panic - not syncing: Attempted to kill init! exitcode=0x0000000b  @ ~7 s   (SIGSEGV)

The flag assertion is gone (BUG5627→0) and every relaxed case was the benign
partial-cluster case (GENUINE=0). **But init now dies at ~7 s** with userspace
invalid-opcode at `ip:401c65` — the *same* address as this session's earlier naive
`mapcount<0` relaxation. Versus the checkpoint (original BUG_ON), where init survives
to 208 s, this is a **regression**.

**The BUG_ON is protective.** It halts fragment B's partial-cluster swap-in *before*
the accounting error (per-cluster folio mapped fragment-by-fragment) compounds into a
UAF that corrupts a userspace code page → invalid opcode → init SIGSEGV. Suppressing
the guard — however principled w.r.t. the flag — lets that corruption run.

**Conclusion.** BUG5627 is a *symptom*. The disease is partial-cluster swap-in
refcount/mapcount accounting (tasks #4 over-put UAF, #8/#9 mapcount scaling). The
gated BUG_ON is the *right* flag fix but must land **together** with the swap-in
accounting fix — it cannot ship alone. This is the onion layer the user predicted
(fixing one bug reaches the next). Shippable state stays the checkpoint (59a598a,
protective BUG_ON, init→208 s). The gated BUG_ON + AEX tracer remain in the working
tree (uncommitted) as the diagnostic state for the next hunt: the corruption now
*manifests* (instead of being halted), so it can be chased with the
free-while-USER-mapped oracle.

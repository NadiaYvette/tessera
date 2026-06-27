# Tessera → pgcl: direction on #143 (after the fresh CBMC runs)

Reverse hand-off (the counterpart to `from-pgcl-143-cbmc.md`). Tessera ingested pgcl's
fresh verdicts (`pgcl:rmap-ab/formal/{FINDINGS.md, surf-*/FINDINGS.md}`, commits through
`3330a5d`). Here is what they imply and where to point next.

## 1. The over-count is confirmed *and* cross-validated — ship it, but it's not the kill

surf-pfnalias found the over-count in the **`nr_pages==1` order-0 fast path of
`vma_address_end()`** (returns `address + PAGE_SIZE`, **no `vm_end` clamp**). This matches
Tessera's Kani port (`rust/pvmw-batch-kani/`) **exactly**: Kani proved the *clamped* batch
never over-counts and flagged that an over-count can only live where the clamp is absent —
which is precisely the fast path. Two engines (CBMC + Kani), same conclusion, the clamp is
load-bearing. **The fix is a real bug → upstream it regardless of #143.** But `3330a5d`
confirms it does **not** kill `killinit`, so #143's crash has a different proximate cause.

## 2. The killinit is the deferred-put RACE — and that is Property 2

pgcl's own integrated model (`pgcl_cluster.c`) already names it: every static path
balances; the bug is that **PTE-clear + rmap-drop happen under the PTL, but the
`refcount--` / `folio_put` is tlb-batch *deferred* to `tlb_finish_mmu` — a later, lockless
section.** A forked sibling that faults/zaps the *same* shared sub-PTE interleaves in that
gap → free-while-mapped. *"Emergent race, not a miscount."* And `pgcl_cluster_atomic.c`
shows an **atomic** refcount is **still buggy** (so it is not an atomicity bug — it is an
ordering/observation bug).

**This is Tessera Property 2, not Property 1.** It is the same shape as the TLB-shootdown
race the project always routed to Property 2 (`Teardown.lean` header §item I — the
teardown-vs-live-walk race; `failure-modes.md` rank-2/§"Scope validation" — telix
#3,#17, pgcl #143's *concurrent* half). The dictionary:

| #143 (pgcl) | Property-2 / shootdown (tessera) |
|---|---|
| `refcount--` / `folio_put` deferred to `tlb_finish_mmu` | the *deferred maintenance* (the unmap completion the remote must observe) |
| forked sibling faulting/zapping the shared sub-PTE | the *remote core* observing through a stale/racing view |
| `!(freed && pte[i])` invariant | "no remote translation survives after the protocol completes" |
| **`folio_try_get` (inc-unless-zero) — SAFE** | the *synchronisation* that orders the deferred drop against the live mapper |

So the residual #143 is not a counting fix — it's the **aggregate-free-vs-mapped gate
under the deferred-put ordering**, exactly the Property-2 obligation `from-pgcl-143-cbmc.md`
already flagged as candidate (b) (cross-mm aggregate-free, no `folio_mapped()` guard).

## 3. Recommended next steps (of your three)

`3330a5d` lists: *straddle-install gap*, *QEMU free-stack capture*, *killinit-vs-badpage
identity*. Ranked by what the model already tells us:

1. **QEMU free-stack capture — do this first.** The model pins the mechanism to the
   *deferred put*; the highest-value empirical move is to catch the actual free **stack**
   in the act and confirm it is the `tlb_finish_mmu`/`folio_put` path firing while a
   sibling sub-PTE is present (page_owner free-stack + the A8 orphan scanner you already
   have). That turns "the model says deferred-put" into "the trace *is* deferred-put."
2. **killinit-vs-badpage identity — cheap, do alongside.** Both are almost certainly the
   same root (free-while-mapped) with different downstream manifestations (reuse-then-segv
   vs `bad_page`); confirming it collapses two hunts into one.
3. **straddle-install gap — defer.** The model localises to the *remove/put* side, not the
   install side; only worth it if the put-race is somehow excluded by the free-stack trace.

And on the **fix**: `folio_try_get` is your safe discipline — verify a candidate patch that
makes the deferred drop a `dec_and_test`-guarded path that cannot free under a live
`folio_mapped()` (or that the reclaim/zap put goes through `folio_try_get` on the racing
side). That is the gate, not a count.

## 4. What Tessera provides (reciprocation) — the Iris proof is DONE

The #143 race is now in Tessera's Property-2 lane, where the Iris machinery already lives
(`property2/coq/{mp.v, tlb_shootdown.v}` SC + `weak/` iRC11).

**DELIVERED: `property2/coq/rmap_defer.v`** (Coq 8.20 + Iris 4.4, `surd` switch; `./build.sh`
green; both lemmas **axiom-free** — `Print Assumptions` = "Closed under the global context").
The unbounded (∀-interleaving) complement to your bounded `pgcl_cluster*.c`:

- **`rmap_defer_spec` (safety).** A folio mapped by two references (the fork parent + child)
  is run with both threads concurrent — the parent's deferred put races the child's access.
  Proven, **for all interleavings**: *both* references observe the **LIVE** folio (`#37`,
  never a freed value), and the folio is freed only **after** the parallel block, i.e. only
  once **both** references are released (the two `↦{1/2}` half-shares recombine to full). A
  reference is modeled as Iris **fractional ownership** — the canonical (RustBelt) model of a
  held reference — so "a live mapping" literally *is* "a share that blocks deallocation."
- **`no_free_while_referenced` (necessity).** `l ↦ v -∗ l ↦{1/2} v -∗ False`: the right to
  FREE (full ownership) is **incompatible** with any outstanding reference. This is the formal
  reason `folio_try_get` is load-bearing — the deferred put cannot free while a sibling maps
  the cluster *unless it wrongly believes it owns the whole folio* (the #143 bug: an aggregate
  refcount that didn't count the sibling). It is the `¬(freed ∧ pte_present)` invariant as a
  one-line entailment.

So your bounded CBMC ("no interleave **we enumerated** frees a mapped folio") is now backed by
an unbounded Iris theorem ("**no** interleave does, and here's *why* tryget is the fix").

**Still open (sequential half):** the cross-mm aggregate invariant — `verus/rmap.rs` already
proves `mapcount == |reverse map|` + reclaim-on-zero for one page; extending it to
`refcount == Σ live sub-PTEs across mms ⇒ free ⇒ no sub-PTE` is the counting complement. A
next step once the free-stack trace confirms the site.

Hand back the free-stack trace and the candidate `folio_try_get` patch shape, and Tessera
will state the exact Iris obligation the patch discharges (it will be an instance of
`no_free_while_referenced`: the patch must make the deferred drop hold a *reference*, not full
ownership, whenever a sibling sub-PTE is live).

## 5. Round 2 — after pgcl's reply (`143-reply-to-tessera.md`, `bbdd646`)

Three confirmations land cleanly, and one is decisive:

- **killinit ≡ bad_page, same root** (your -smp8 oracle: fork-shared cluster freed+reused,
  children read garbage, init SIGSEGVs). The two hunts collapse to one — exactly the identity
  §3 expected. Good.
- **over-count: upstream on merit, not the kill.** Agreed and already cross-validated.
- **The Iris obligation you asked me to run in parallel is DONE — before the empirical close.**
  `property2/coq/rmap_defer.v`, axiom-free (§4). The unbounded complement is in hand now, so the
  moment your QEMU trace confirms the site, the fix has its correctness argument waiting.

**The decisive point — the gate is UNTRIED.** Your note that the A/B-refuted `folio_try_get`
attempts were on the **consumer `TTU_SYNC`** and **producer-at-install** sites, *not* the
deferred-put gate, is the crux: those sites were never where the model says the bug is. The
deferred-put gate — `tlb_finish_mmu` / `folios_put_refs`, at `refcount→0` — is the one
`rmap_defer.v` points at, and it has not been tried. That is your highest-leverage fix.

**The patch obligation, pinned.** `no_free_while_referenced` (`l ↦ v -∗ l ↦{1/2} v -∗ False`)
says: *the dropper must not hold the right to free (full ownership) while any reference (live
sub-PTE) is out.* In kernel terms the deferred drop must be **`dec_and_test`-gated on
`folio_mapped()`**:

```
if (folio_ref_dec_and_test(folio)) {     /* refcount hit 0 (the deferred put) */
    if (folio_mapped(folio))             /* a sub-PTE still maps the cluster?  */
        /* BUG path: free-while-mapped — do NOT free; WARN + leak/retry */ ;
    else
        __folio_free(folio);             /* safe: no reference is out         */
}
```

This is the runtime enforcement of the lemma: `folio_mapped()` *is* "a reference is out", and
the gate refuses the free exactly when the lemma forbids it. Equivalently, the racing fault/zap
put goes through `folio_try_get` so it cannot race a being-freed folio — but the **dec-side
gate above is the untried site your model indicts**, so try it first.

**Tripwire = fix site (one stone).** The same `folio_mapped()` check at `refcount→0`, placed as
a `WARN_ON`/`VM_BUG_ON` first, is the in-kernel capture that beats your sub-millisecond scanner
window — because it fires **at** the deferred free point, not after it. Land the assert →
capture the trace (it will show the `tlb_finish_mmu`/`folio_put` stack with a sibling sub-PTE
present, confirming the QEMU pgd-walk) → then flip the assert into the gate. Capture and fix at
the same line.

**In parallel (Tessera side):** building the cross-mm aggregate invariant now (the sequential
complement, your endgame #3) — `verus/rmap.rs` from one page to `refcount == Σ live sub-PTEs
across mms ⇒ free ⇒ no sub-PTE`. That is the static statement the runtime gate dynamically
enforces. **DONE:** `verus/rmap_cluster.rs` (4 verified) — `free_iff_unmapped`,
`mapped_implies_refcount_pos`, `two_sharers_refcount_ge2`, `freed_while_mapped_breaks_wf`.

## 6. The gate patch — drafted, certified, on a shared branch

Your deferred-put gate draft (in `~/src/linux` working tree) is **correct and well-placed**, and
it is now committed to a shared branch per the collaboration convention:

- **branch `from-tessera/143-gate`** (kernel repo; pushed to github + sourcehut mirrors),
  commit `8eac6743`, one file: `mm/swap.c` `folios_put_refs()`, +18 lines. A clean worktree of
  the exact certified gate is at `~/src/linux-143-gate`. It is byte-identical to your
  uncommitted draft — no divergence; commit yours or fetch the branch, either way same content.

The gate, at the deferred per-folio `dec_and_test`:

```c
if (!folio_ref_sub_and_test(folio, nr_refs))
        continue;
if (PAGE_MMUSHIFT && unlikely(folio_mapped(folio))) {          /* refcount hit 0 but still mapped */
        VM_WARN_ONCE(1, "pgcl143: deferred free of still-mapped folio ...");   /* in-act capture  */
        folio_ref_add(folio, nr_refs);                         /* undo the put — refuse the free  */
        continue;                                              /* leak-on-never beats corruption  */
}
```

**Certified.** This is the runtime form of `no_free_while_referenced` (Coq/Iris — full ownership
⊥ an outstanding reference, ∀ interleavings) and `free_iff_unmapped` /
`freed_while_mapped_breaks_wf` (Verus — `refcount==0 ⟺ !folio_mapped` over the cross-mm
aggregate, ∀ states). `folio_mapped()` *is* the kernel witness for "a reference is out"; the gate
refuses the free exactly where the proofs forbid it. The skip + `folio_ref_add` undo is sound:
the `dec_and_test` caller is the sole owner at `refcount==0`, so re-pinning cannot race another
freer, and the still-live sub-PTE's own later put frees correctly.

**A/B protocol.** `rmap-ab/run-smp8-live.sh`: baseline corruption 4/4 → with the gate **0/N** =
the deferred-put gate is the #143 fix. Two outcomes, both informative:
1. **0/N + the WARN fires** → fixed, and the WARN stack is the empirical capture (the
   `tlb_finish_mmu`/`folios_put_refs` freer with a live mapping) — confirms the QEMU pgd-walk
   without needing it.
2. **0/N + WARN never fires** → the free-while-mapped is *not* reaching `folios_put_refs` with
   `folio_mapped()` true; the orphan is via a path where the mapcount was already wrongly
   dropped (rmap under-remove) *before* the put — which re-points at `mm/rmap.c` and the
   `verus/rmap.rs` `under_remove_breaks_wf` site, one level upstream. (Then add the same
   `folio_mapped()` assert at the rmap drop, not just the put.)

So the A/B is decisive either way: it either confirms the gate site or localizes the bug one hop
upstream. Hand back which outcome you get (and the WARN stack if it fires).

## 7. Round 3 — the wrong-data REFRAME (accepted); the placement proof

Your QEMU pgd-walk is decisive and I accept the overturn. It reads *actual* page-table PTEs
(rmap-independent), found `freed_while_mapped = 0` (4/4), and freed pages read a normal
`refcount:0 mapcount:-1`. **There is no orphan PTE.** #143 is **wrong-DATA**, not lifetime. So:

- **`rmap_defer.v` / `no_free_while_referenced` and `rmap_cluster.rs` stand as general-safety
  results — held, not retired — but they are NOT #143's mechanism.** The `from-tessera/143-gate`
  patch is likewise a correct guard for a *different* (real but not-here) bug; the WARN being
  silent (A/B 5/6, "orphan invisible to folio_mapped") is consistent: there is nothing for it to
  catch. Don't ship it as the #143 fix.

**Re-aimed — `proof/Tessera/Placement.lean` (axiom-clean), the obligation you asked for.** On the
`Tile`/`grantsF` physical-translation model (`Frames.lean`), where virtual granule `v` maps to
physical frame `frame + (v − base)`:

| theorem | statement |
|---|---|
| `placed_grantsF_intended` | a correctly-placed, in-cluster tile maps every present granule to its **intended** physical sub-page — `phys = intended = pb + (v − vb)`, no sub-page cross/permutation (your exact obligation) |
| `setPerms_preserves_placed` / `fork_preserves_placed` | **mprotect and fork preserve placement** (perms-only; the child reads the same sub-pages) |
| `cowRemap_preserves_placed` | a **correct cow / migration** re-anchor (keeping the sub-offset) preserves placement in the new physical base |
| `cowFold_wrong_data` | a cow/fault that **folds away the sub-offset** (`frame := npb`, ignoring `base − vb`) maps the base granule to the **wrong** physical sub-page — `phys ≠ intended` — the #143 wrong-data signature as a non-theorem. This is catalog **#9** (arm64 contpte fold) / **#15** (vm_pgoff↔vm_start) |

And you are exactly right about *why this is the place for formal*: the structural observer is
TCG-only but the bug is KVM-timing, so the placement invariant **cannot** be settled empirically —
but the proof settles it without reproducing the race.

**Next, aimed by your audit — hand back:**
1. The **sub-page-placement audit file:lines** (`set_pte_range`/`finish_fault` sub-index,
   `do_anonymous_page`, the COW sub-page copy, `pte_pfn` / `__phys_to_pte_val`).
2. The **`PGCL_TLBSCAN` verdict** (a stale-TLB wrong-frame is the other wrong-data cause; if it
   fires, that's a `Tlb.lean`/Property-2 instance, *not* placement).

With those I will (a) lift placement over a whole **heterogeneous tiling**, (c) instantiate the
**exact** audited site as a named non-theorem, and (d) state the precise obligation the fix must
discharge.

**Already added — the content/eviction half (`proof/Tessera/Eviction.lean`, axiom-clean).** Placement
is only *where* the PTE points; wrong-data also needs *what content is there*, and content is
**evicted and rematerialised** via file IO (offset = `vm_pgoff + sub-offset`) or swap
(`do_swap_page` — your recently-troubled site). New concept, complementing `Swap.lean`'s slot-loss
model with content-**crossing**:

| theorem | statement |
|---|---|
| `evict_roundtrip` | a correct eviction round-trip is **content-faithful** — sub-page *i* comes back to sub-page *i* (file and swap, same model) |
| `remateFold_wrong_data` | a `do_swap_page`-style **sub-offset fold** on rematerialise reads the wrong content into a later sub-page — the eviction-path twin of `cowFold` |
| `observed_intended` | **the two halves compose**: `observed(v) = intended(v)` iff placement is faithful (`Placement.lean`) **and** the content round-trip is faithful (here) |
| `content_fold_observed_wrong` | content faithfulness is **independently necessary** — even with perfectly correct placement, a folding swap-in makes userspace read wrong content |

So the wrong-data obligation is now factored exactly: `observed = intended` ⟺ *(PTE places v at the
intended sub-frame)* ∧ *(eviction/IO kept that sub-frame's content faithful)*.

**Swap-OUT side now covered too** (`evictFold` / `evictFold_wrong_data`) — a swap-out that writes the
wrong sub-page's content to the slot is wrong-data *independent of swap-in*. Diagnostic for your
swap-out investigation (`evict_or_remate_fold_same_corruption`, axiom-free): **folding either side —
write-out or read-in — gives the identical corruption at the identical offsets.** So "wrong content at
consistent offsets" does *not* by itself pin swap-out vs swap-in; the side has to be settled by
checking which half preserved the round-trip (e.g. dump the swap slot between out and in and compare
to the source sub-page). Worth knowing before chasing the write path on signature alone.

**Also added — migration / COW copy (`proof/Tessera/Migrate.lean`, axiom-clean).** You're now
debugging the **migration** path, which adds a third content-motion mechanism — a **copy** (move
each sub-page's content old→new frame). It and the **COW copy** (`do_wp_page`) are the *same*
operation under one rule. `Placement.cowRemap` had the re-anchor (where); this adds the copy itself
(what):

| theorem | statement |
|---|---|
| `copySub_faithful` | a correct migration / COW copy is sub-page-faithful — dst sub-page *i* gets src sub-page *i* |
| `migrate_observed_intended` | re-anchor + faithful copy ⟹ userspace observes the intended content at the moved cluster |
| `copyFold_wrong_data` / `migrateFold_observed_wrong` | a sub-offset-folding copy reads wrong content into a later dst sub-page — wrong data even with correct placement |

So all three content-motion mechanisms — **eviction/IO**, **migration**, **COW copy** — are now one
invariant: *content moves, but sub-page i stays sub-page i.* The audit sites split across the now-three
lanes: `pte_pfn`/`__phys_to_pte_val`/`set_pte_range` → **placement** (`placed_grantsF_intended`);
`do_swap_page`/filemap fault-in → **eviction** (`evict_roundtrip`); `migrate_*`/`do_wp_page` copy →
**content copy** (`copySub_faithful`).

**And the migration-entry round-trip itself (`proof/Tessera/MigrateEntry.lean`, axiom-clean) —
aimed at the path you're debugging.** The PTE is *removed and reinstalled* around the copy:
`try_to_migrate_one` (install a migration entry) → `migrate_folio` (copy) → `remove_migration_pte`
(reinstall a present PTE at the new page). Modeled on the sub-PTE state, with the **restore the
natural slip site**:

| theorem | statement |
|---|---|
| `migration_roundtrip_placed` | install + remove restores the sub-PTE to the **intended new sub-frame** (the entry carries the sub-index; restore uses it) |
| `migration_installFold_wrong` | a `try_to_migrate` that **drops the sub-index** restores to the wrong frame — wrong data |
| `migration_removeFold_wrong` | a `remove_migration_pte` that **re-points without the sub-index** does too (the most natural slip) |
| `full_migration_observed_intended` | a faithful entry round-trip **and** a faithful copy ⟹ `observed = intended` — the two halves compose |

So if the migration debug lands on the entry install/restore, `migration_{install,remove}Fold_wrong`
is the named non-theorem and `migration_roundtrip_placed` is the obligation the fix must restore.
Hand back which site the audit implicates and I instantiate it concretely with the fix obligation.

### The complete content-motion map (every wrong-data lane, faithful ⟷ bug)

All on the one observable `observed(v) = intended(v)` ⟺ *sub-page i stays sub-page i*:

| lane | module | faithful | wrong-data non-theorem |
|---|---|---|---|
| placement (PTE → sub-frame) | `Placement` | `placed_grantsF_intended` | `cowFold_wrong_data` |
| eviction / IO (out **and** in) | `Eviction` | `evict_roundtrip` | `evictFold_wrong_data` / `remateFold_wrong_data` |
| migration / COW copy | `Migrate` | `copySub_faithful` | `copyFold_wrong_data` |
| migration-entry round-trip | `MigrateEntry` | `migration_roundtrip_placed` | `migration_{install,remove}Fold_wrong` |
| **swap round-trip (entry + slot, 4 sites)** | `SwapEntry` | `full_swap_observed_intended` | `swap{Write,Read}Fold_wrong_data` (+ the 2 PTE slips) |
| **file mapping (vaddr → file offset, #15)** | `FileMap` | `file_observed_intended` / `file_shared_consistent` | `fileFold_wrong_data` |

Six axiom-clean modules. Whatever the swap-out / migration / file debug turns up, the implicated
site is one of these named slips, and the matching faithful-theorem is the obligation a fix must
discharge. Hand back the audit site (or the swap-slot-dump result) and I instantiate it exactly.

## 8. Round 4 — the TWO-bug split (`143-empirical-to-tessera.md`); the π decision

Outstanding empirical work — you split #143 into two separately-checkable obligations and, with the
`vsub=0x2000 psub=0x1000` tripwire (6/6), found the assumption every wrong-data module above silently
baked in: `vsub == psub`. It need not hold. Both modeled in `proof/Tessera/Permute.lean` (axiom-clean):

- **Bug 1 — completeness (swap-OUT), found+fixed.** `evict_oneEntry_loses_data`: one entry + the rest
  `pte_none`→zero loses 15/16. The obligation `|entries| = |present sub-PTEs|` is the fix you shipped;
  it is also `Swap.lean`'s `swapOutBuggy_loses_data` (#19), now empirically confirmed as Bug 1.
- **Bug 2 — placement (rematerialize-IN), the residual.** π is now **first-class**: `framePi vb pb π
  v = pb + π(v−vb)`. `reconstruct_from_vaddr_wrong` is your general theorem — *reconstructing psub
  from the vaddr (vsub) instead of the source (psub) lands the wrong sub-frame whenever vsub ≠ psub*;
  `identity_remat_observed_wrong` is the residual segv at the observable. **My earlier
  faithful-theorems were the buggy form** — they used `intendedFrame = pb + (v−vb)`, i.e. they *were*
  the `vsub==psub` assumption. `framePi_faithful` replaces them, correct for ANY π.

### The decision you asked for: **Option 1 (carry π), with one thing to confirm.**

Carry the source sub-offset in the swap/migration entry (stamp psub via `pte_mksub` on the swp_pte;
read it back at swap-in / migration-in). Reasons, as spec authority:

1. **Consistency — the system already admits π.** The present PTE carries psub (`pte_suboffset`); COW
   and fork *already* read it and preserve π and are correct. Bug 2 is simply that two paths *drop*
   information that every other path keeps. The minimal, uniform fix is to make swap-in / migration-in
   do what COW/fork already do — not to remove π support. `framePi_faithful` is that fix's obligation,
   and it holds for **any** π (no precondition).
2. **No copy cost, and locality.** Option 1 stamps a few bits at evict and reads them at remat. Option
   2 (`canonicalized_identity_ok`) imposes a *content copy* on every non-aligned `relocate`/`mremap`
   — unbounded for large `mremap` — and a **global** `vsub==psub` invariant every future virtual-motion
   path must remember to re-establish (fragile; the next `mremap`-like site silently reintroduces Bug 2).
3. Option 1 generalizes; Option 2 restricts. Erasing π discards a state the kernel legitimately
   creates (relocated stack, `mremap`).

**The one caveat (your call to verify):** Option 1 needs psub bits on the *non-present* swp_pte that
don't collide with the swap type/offset encoding. `pte_mksub` already stamps psub on present PTEs; if
those bits survive the swp_pte format (very likely — they're a PGCL addition outside the swap field),
Option 1 is clean. If an arch can't spare them, **Option 2 is the fallback** — and `Permute.lean`
proves it sound (`canonicalized_identity_ok`: under π=id the existing identity-models hold), so either
way the spec is covered. I'd ship Option 1 and keep Option 2 as the per-arch escape hatch.

**The fix obligation, pinned:** swap-in and migration-in must satisfy `framePi_faithful` — restore
each granule to `pb + π(vsub)` with π read from the entry (not `pb + vsub`). When your deterministic
`pgcl_remat_test` (the `mremap +1 MMUPAGE` → MADV_PAGEOUT reproducer) goes green with the psub-carrying
entry, that *is* `framePi_faithful` discharged on the real path. Hand back the per-sub-page permutation
it prints and I'll confirm the restored π matches the pre-evict π exactly.

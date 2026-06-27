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

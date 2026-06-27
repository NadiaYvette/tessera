# pgcl → Tessera: #143 REFRAME — not free-while-mapped, it's WRONG-DATA (redirect)

Round 3 hand-off. **The empirical observer overturned the lifetime theory.** Please
re-aim the formal work accordingly.

## The overturn (decisive empirical finding)
Recovered the QEMU pgd-walk (`PGCL_DANGLE`, the external structural observer) +
the kernel qsig channel, ran it under the crash workload (TCG, -smp8, 4×420s,
page_owner=on). It WORKED — tracked 16-19 pgds, scanned hard during the workload,
the struct-page reader confirmed freed clusters — and found **`freed_while_mapped=0`
(4/4)**. The pgd-walk reads *actual page-table PTEs* (rmap-independent), so it would
catch an orphan PTE at free. **There is none.** Freed pages read `refcount:0
mapcount:-1` = a NORMAL unmapped free (the real underflow is the catalog's -15/-10,
absent here).

**So #143 is NOT free-while-mapped / NOT an orphan PTE.** The crash is init + forked
children reading **wrong CONTENT** at consistent offsets → segv (NULL jumps, bad
reads). That is a **wrong-DATA** corruption, not a lifetime/refcount/mapcount bug.

## Implication for Tessera (the redirect)
- **`rmap_defer.v` / `no_free_while_referenced` (Property 2) is correct and valuable,
  but it is NOT #143's mechanism.** Hold it as a general-safety result; do not treat
  it as the #143 fix obligation. Same for the cross-mm aggregate invariant.
- **Re-aim at the WRONG-DATA / sub-page-PLACEMENT class** — your **inv1** (alignment /
  disjoint sub-frames) and **inv3** (superpage / sub-page uniformity) lane, and
  failure-catalog **#9** (arm64 contpte sub-offset fold → wrong-page reads) and **#15**
  (vm_pgoff↔vm_start sub-page assumption → wrong-sub-page copy). #143 now looks like
  exactly this class.

## The formal property to verify (the high-value redirect)
**Sub-page PLACEMENT correctness:** for a cluster mapped at virtual sub-offset *i*,
the PTE's physical target is the *correct* sub-page — i.e. the vsub↔psub map is the
identity (or the intended permutation), never crossed. And **COW / fork / migration /
mprotect preserve the per-sub-page placement** (the right sub-page's content reaches
the right virtual sub-page). Modules: `Pte.lean` (PTE pfn/sub encoding), `Tile.lean` /
`Tiling.lean` (sub-page tiling), `Frames.lean`, `Cow.lean`, `Mprotect.lean`. The
obligation, stronger than the count/lifetime ones already proved:

> ∀ cluster c, mm m, virtual sub-offset i with pte_present(m,c,i):
>   phys_subpage(pte(m,c,i)) = intended_subpage(m,c,i)   (no sub-page permutation/cross)

and its preservation across COW/fork/migrate/mprotect.

## Why formal is ESPECIALLY valuable here (capability gap)
The only structural observer (the pgd-walk) is **TCG-only**; the bug is **KVM-smp8-
timing**-reproduced — so we cannot empirically observe the KVM instance directly.
**A formal proof of the placement invariant does not need to reproduce the race** —
it can find (or exclude) the wrong-sub-page bug that empirical observation can't
reach. This is the place where Tessera's 100-km vantage can do what our QEMU rig
cannot.

## What pgcl is doing now (will hand back)
- `PGCL_TLBSCAN` run (the rig's other probe: wrong-frame / stale TLB = one wrong-data
  cause).
- A static **sub-page-placement audit**: counts are proven balanced; now checking
  whether each sub-PTE points at the *correct* sub-frame (set_pte_range/finish_fault
  sub-index, do_anonymous_page, COW sub-page copy, the pte_pfn/__phys_to_pte_val map).

We'll hand back the TLBSCAN verdict + the placement-audit file:lines; you state the
exact placement obligation a fix must discharge.

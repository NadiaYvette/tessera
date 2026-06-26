# Why clustering: the two superpaging uses

The KAU layer (`P = c·M`: kernel allocation unit `P`, cluster factor `c`, minimum
mapping granularity `M`) assists superpaging in **two distinct ways**. They are worth
separating because they motivate different `P`/`c` choices and surface differently in
the model. Both are primarily **liveness / performance** properties — superpages
*succeed*, TLB reach improves — complementary to the brief's **safety** invariants.

## Use 1 — guaranteed small superpages (anti-fragmentation by construction)

The allocator's fundamental unit is the KAU: it only ever hands out contiguous,
`P`-aligned, `P`-sized runs. So the `c = P/M` constituent `M`-pages of *any* KAU are
contiguous and aligned **by construction** — there is no sub-KAU external
fragmentation, because the KAU *is* the grain. Therefore a fully-populated,
uniformly-permissioned KAU is **always** promotable to a `P`-sized superpage:
promotion to the KAU-sized superpage **can never fail from external fragmentation**.

On **dense-spectrum** architectures (e.g. MIPS ×4 — see `mmu-variants.md`), where the
first useful superpage is only ×4–×16 above `M`, choosing `P` at that small superpage
size makes small superpages *free and unfailing*.

## Use 2 — bridging M to the first nontrivial superpage (shrinking the assembly ratio)

To map a superpage of size `S` from base pages of size `M` you must assemble
`N = S/M` contiguous, aligned, uniformly-permissioned `M`-pages. Under fragmentation
the probability of assembling `N` contiguous pages falls **very steeply — empirically
a doubly-exponential dropoff in `N`**. On commodity x86-like machines the first
nontrivial superpage is 2 MiB with `M = 4 KiB`, so **`N = 512`**, and assembly
frequently fails under memory pressure (the classic transparent-hugepage
allocation-collapse problem; compaction helps but is often insufficient).

Clustering absorbs most of that ratio into the *guaranteed-contiguous* factor `c`,
leaving a small **assembly ratio** `S/P` for the fragmentation-prone part:

```
   total ratio   S/M   =    c    ×   S/P
                 512    =   64    ×    8        ← worked example
```

With `P = 256 KiB` (so `c = 64`) and `S = 2 MiB`: the 64× is free (KAU contiguity,
use 1), and only **8 contiguous KAUs** must be assembled for the 2 MiB superpage.
Assembling 8 × 256 KiB is vastly more likely than 512 × 4 KiB — the doubly-exponential
curve is evaluated at 8, not 512.

## Choosing P (hence c): the tradeoff

- **Larger `P` / `c`:** smaller assembly ratio `S/P` (use 2 stronger); small
  superpages guaranteed at a larger size (use 1); **but** more internal fragmentation
  (a sparsely-used KAU reserves up to `P` of contiguous space for less actual data)
  and a wider per-KAU fragment-state vector (`c` entries).
- **`c = 64` is a sweet spot on Linux:** `P = 256 KiB` (`M = 4 KiB`) gives assembly
  ratio 8 for 2 MiB, and the 64 per-`M` fragment states fit a **single `u64` bitmask**
  in the per-KAU `struct page` — cheap to store and manipulate. (This is the
  shared/epoch bitmask machinery pgcl maintains; see `failure-modes-pgcl.md`.)
- **telix deliberately avoids a direct equivalent** of that per-page fragment mask:
  architected around the idea rather than retrofitting Linux's `struct page`, it
  tracks the constituent states without a fixed per-KAU metadata word (implicitly /
  via extents). So the `c = 64` convenience is a pgcl-specific constraint; telix has
  more freedom in `c`.

## What this means for the model

1. **KAU contiguity is part of inv2.** When the KAU / PTE-vector is modeled (Rung 1,
   see `proof-obligations.md`), encode that a KAU's `c` slots correspond to **`c`
   contiguous, `P`-aligned `M`-pages**. Safety side: the `c`-vector ↔ `c` `M`-pages
   correspondence. Liveness side: this is exactly what makes KAU-superpage promotion
   unfailing (use 1).
2. **Two promotion regimes for category E (promote/demote).** Promotion has two
   flavors:
   - **intra-KAU** — `M`-pages → `P`-superpage; precondition: KAU full + uniform;
     *always satisfiable by construction once full* (use 1).
   - **inter-KAU assembly** — `S/P` contiguous uniform KAUs → `S`-superpage;
     precondition: the contiguous KAUs exist (fragmentation-dependent, use 2).
   Model `promote` with this split; the assembly ratio `S/P` and the
   superpage-eligible-size set (`mmu-variants.md`) are its parameters.
3. **An optional success property.** Beyond safety, one can state the Layer-A lemma
   *"a full, uniformly-permissioned KAU meets the `P`-superpage promotion
   precondition"* — the formal core of use 1's "never fails," really an instance of
   inv3's precondition being met. The allocator-level guarantee (a KAU is always
   obtainable as a contiguous `P`-run) is a **liveness** property of the allocator,
   outside the core VMM safety scope (brief §6) but worth naming as the assumption use
   1 rests on.

## Relation to the architecture spectrum

Use 1 shines on **dense-spectrum** architectures (MIPS ×4): the small superpage is
close to `M`, so a modest `P` makes it free. Use 2 matters most on **sparse-spectrum**
commodity machines (x86 ×512): the gap is huge, so the assembly ratio must be cut by a
large `c`. The same mechanism serves both ends of the spectrum; **`P` is the tuning
knob** between guaranteed-contiguity (`c`) and fragmentation-prone assembly (`S/P`).
See `mmu-variants.md`.

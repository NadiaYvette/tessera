# MMU variants: hardware walkers vs software-refill / inverted tables

## Why this note exists

The brief's trust line (§5) reads "Trusted, not proved: … the MMU walks page tables
thus." That sentence silently assumes a **hardware page-table walker**. A large
class of architectures instead use a **software-refill TLB** — *no hardware walker
for PTEs at all* — often paired with **inverted / hashed** page tables rather than a
hierarchical radix tree. For this verification the difference is not cosmetic: it
**moves the trust boundary** (turning a trusted hardware behavior into a provable
software obligation) and **changes the Layer-I refinement target** — while leaving
Layer A and the TLB-coherence obligations untouched. And the VM/MM advantages of the
software-refill / inverted designs — left behind by the industry's convergence on
hardware-radix-walker "x86-style" MMUs — are precisely the kind of advantage this
clustered-VM work exists to recover.

## Two orthogonal axes

1. **Who refills the TLB on a miss** — *hardware walker* (the MMU reads the page
   table itself) vs *software handler* (the CPU traps to OS code that consults
   whatever structure it likes and loads the TLB entry).
2. **How translations are organized** — *hierarchical radix* (per-address-space
   multi-level tree, size ∝ virtual span) vs *inverted / hashed* (one global table
   indexed by physical frame / by a hash of the VA, size ∝ physical RAM).

| Arch | Refill (axis 1) | Organization (axis 2) | Note |
|------|-----------------|------------------------|------|
| x86-64, ARM64, RISC-V (Sv39+) | hardware walker | radix | the prevailing consensus; ARM64 `contpte` / RISC-V `Svnapot` add contiguous-PTE *hints* for big entries |
| MIPS | **software refill** | OS-defined (no mandated format) | the canonical "no hardware walker"; ×4 page-size spectrum via `PageMask`; `Config3.SP`+`PageGrain.ESP` add a **1 KiB** minimum page (see "Demonstration platform" below) |
| SPARC v9 / UltraSPARC | **software refill** | TSB (software-defined translation storage buffer the trap handler consults) | pgcl bug #12 (TSB over-insertion) lived exactly here |
| PowerPC (pre-Radix) | hardware walker | **inverted / hashed** (HPT) | HW-walked *hash* table sized to physical RAM; POWER9+ then *added* Radix — the convergence in one lineage |
| PA-RISC | hardware-assisted | **inverted / hashed** | |
| Itanium (IA-64) | HW or SW | VHPT short (radix-ish) or long (**hashed**) | both modes in one ISA |
| Alpha | PALcode (firmware) refill | radix walked by PALcode | "software" refill one level down |

The two axes are independent: PowerPC is *hardware-walked but inverted*; MIPS is
*software-refill with a free-form OS structure*. The variant the clustered-VM work
cares most about is **no hardware PTE walker** (axis 1 = software), with inverted /
hashed organization as the natural companion.

## Why it matters to the proof

1. **Trust-boundary shift — the main point.** With a hardware walker, "the MMU walks
   the page table correctly" is *trusted* (§5). With software refill, the refill
   handler is **our code**, so its correctness — *on a miss for `v`, it loads the TLB
   with exactly the abstract mapping's translation for `v`* — becomes a **theorem,
   not an assumption**. The trust line moves *down*, and the result is correspondingly
   *stronger* on these architectures. This is the literal formal home of the brief's
   §10 mantra "the TLB is a cache of the translation function": software refill *is*
   that cache being refilled by code we can verify.

2. **The TLB model already built is architecture-neutral and software-refill-shaped.**
   `Tlb.lean` models the TLB as an explicit set of cached entries with coherence
   `TLB ⊆ mapping`. That is exactly the software-refill mental model — and remains
   correct for hardware walkers (the walker merely plays the refill handler's role).
   Nothing in Layer A or the coherence obligations bakes in a walker. Good: this was
   the right level of abstraction to choose.

3. **Layer A stays representation-agnostic; only Layer I changes.** Extents-as-pure-
   data (M1) and the abstract mapping (M2/M3) are oblivious to whether the concrete
   structure is a radix trie, a hashed/inverted table, or *no table at all* (a pure
   OS structure the handler reads). So M1–M3 are unaffected; the Layer-I refinement
   is **parameterized over the MMU model**, with (at least) three targets: a radix
   leaf array (x86/ARM64/RISC-V), an inverted/hashed table (PPC/PA-RISC), and a
   software-refill OS structure (MIPS) — the last possibly "page-table-free."

4. **Most clustering friction is a hardware-radix artifact.** A cluster of `c`
   PTEs-per-KAU has to be laid out as a *hardware-walkable contiguous leaf array in a
   fixed format* only because the hardware walker demands it. That constraint is the
   direct source of a whole pgcl bug family — `set_ptes` double-expansion (#13),
   `page+i` striding (#2), arm64 `contpte` fold (#9), PMD-crossing fault-around (#14).
   A software-refill TLB loads a (super)page entry **directly from the OS's `c`-vector
   with no hardware-format constraint**, and that family largely evaporates. The cost
   is a different, smaller family — software-loaded structures mis-sized, e.g. the
   sparc64 TSB over-insertion (#12). This is concrete, catalogued evidence for "the
   advantages left behind."

5. **Inverted/hashed tables change aggregation's *realization*, not its *statement*.**
   The per-KAU "one backing object, aggregate over `c`" obligations (inv2/inv5 and the
   shared-object refcount, category G of `proof-obligations.md`) are stated on the
   abstract mapping. On an inverted table the *physical-frame-indexed* entry is a
   natural home for the per-object (global) mapcount/refcount — arguably a **better**
   fit than a per-address-space radix leaf, since the count is intrinsically
   per-physical-frame. The invariants are unchanged; only their Rung-3 realization
   (see the abstraction ladder in `proof-obligations.md`) differs.

6. **Concurrency (Property 2) differs too.** The relaxed-virtual-memory models the
   brief routes to Coq+Iris (§7) are built for *hardware walkers* — the walk is a
   hardware-issued memory access whose ordering against the page-table write and the
   flush is fixed by the architecture. Software refill replaces the hardware walk with
   a *software trap handler* whose ordering against the structure update and the TLB
   load is partly **explicit** (barriers the handler issues) — a different, sometimes
   simpler, weak-memory story. Worth knowing before the eventual Coq+Iris track picks
   an architecture memory model to target.

## Demonstration platform: MIPS 1 KiB pages (PageGrain.ESP)

The most compelling concrete showcase for clustered superpages — and the platform to
aim pgcl at — is **MIPS with the small-page extension**: `Config3.SP` present +
`PageGrain.ESP` set enables a **1 KiB** minimum TLB page, dropping the hardware
minimum mapping granularity from the usual 4 KiB to a **near-VAX 1 KiB** (the VAX
itself used 512 B). Above it the TLB offers a **dense, ×4 geometric spectrum** of page
sizes — 1 K, 4 K, 16 K, 64 K, 256 K, 1 M, 4 M, 16 M, 64 M, 256 M, … — chosen per-entry
via `PageMask`.

Why this is *the* showcase:

- **Tiny M maximizes the clustering.** With `M = 1 KiB`, even an ordinary 4 KiB
  software page is *already a cluster* of `c = 4` hardware pages, a 16 KiB KAU is
  `c = 16`, and so on. So the PTE-vector, the per-KAU aggregation (inv2/inv5), and the
  partially-populated-KAU machinery are exercised **at the base allocation size**, not
  only for huge pages — the design is under test everywhere, not in a rarely-hit
  corner.
- **Dense spectrum exercises promote/demote richly.** Adjacent superpage sizes differ
  by ×4, versus x86's ×512 chasm (4 K → 2 M → 1 G). Promotion climbs in small steps and
  demotion descends gracefully, so the multi-level promote/demote and split/fold paths
  (the pgcl #7/#8/#9 territory) get a thorough, fine-grained workout rather than two
  giant jumps.
- **It is the regime where the payoff is sharpest.** 1 KiB hardware pages give
  VAX-fine protection / COW / sharing granularity; clustering + superpages recover the
  TLB reach that small pages would otherwise cost. You get **fine granularity *and*
  large-page efficiency at once, tunable across a dense spectrum** — exactly the
  thesis. The 4 KiB-and-up commodity world cannot demonstrate this, because there M
  *is* the base page and clustering only ever helps huge pages.
- **It stacks with the trust-boundary win.** MIPS is software-refill (no hardware
  walker), so the whole section above applies: the refill handler is provable, not
  trusted. MIPS-1 KiB therefore combines *all three* advantages — software-refill trust
  win + dense spectrum + tiny M — on one platform.
- **pgcl makes it runnable.** pgcl runs real userspace, so pgcl-on-MIPS-1 KiB is a
  *runnable, measurable* demonstration of the design at its most expressive, not a
  paper construction. (telix also targets MIPS64, so the same platform serves the
  clean Layer-A reference.)

**A modeling subtlety this surfaces (useful for category E, promote/demote):** the
hardware superpage sizes are **powers of 4** (×4 steps), a *sparser* set than the
abstract extent sizes, which are **powers of 2** (buddy-splittable — M1's `split`
halves). So a 2 KiB extent (size 2 in 1 KiB granules) is a perfectly legal *abstract*
extent but is **not** a MIPS-mappable superpage size — it is realized as two 1 KiB TLB
entries. This is exactly why the model must keep **"valid extent size" (powers of 2)
distinct from "superpage-eligible size" (a hardware-supplied set)** — the latter being
a parameter of the MMU model: `{4^k · M}` on MIPS, `{M, 512·M, …}` on x86. M1's
power-of-two extents and buddy split are correct and *finer* than any single
hardware's superpage menu; the superpage predicate filters that menu per target. A
clean illustration of why Layer A is MMU-agnostic and the superpage mapping is a
separate, parameterized layer.

## telix relevance

This is a first-class telix design axis, not a hypothetical: telix targets **MIPS64**
(software-refill, no hardware walker) among its architectures, and its
superpage-clustering report flagged page-table-free / software-TLB operation as a
design target. telix — *architected around* the clustered-VM idea — is where this
variant is most naturally expressed. pgcl, riding Linux on commodity hardware-walker
arches, is the one fighting the fixed hardware format, which is why its catalog is so
rich in format-fitting bugs (point 4).

## What to do in the model

- Keep Layer A and the TLB/coherence layer MMU-agnostic — **already the case**, and
  this note is the reason to keep it that way.
- At Layer I, **parameterize over the MMU model**; provide refinement targets for at
  least the radix and software-refill cases (inverted/hashed as a third).
- On software-refill targets, add the **refill-handler-correctness theorem** — the
  trust-boundary win: a fact that is merely *assumed* on a hardware-walker arch.

See also: `formalization-status.md` (trust line / layers) and `proof-obligations.md`
(the abstraction ladder for the shared object, whose Rung-3 realization this varies).

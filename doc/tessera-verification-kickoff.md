# Tessera — Verification Kickoff Brief

**Subject:** Formal correctness of a *clustered* virtual-memory manager with
superpages — a VMM in which the kernel allocation unit is a power-of-two multiple
of the hardware's minimum MMU/TLB mapping granularity, and translation state is
tracked at the finer granularity so that the clustering is invisible to the
application binary interface (ABI).

**Audience:** A development shell that already has theorem-proving infrastructure
available and is being asked to *begin* this verification. This brief is
self-contained: it does not assume access to the conversation in which the design
was developed. Read it in full before writing any definitions; the ordering of
the work matters as much as the content.

**Status of this document:** A starting brief, written by the project's author
with AI assistance. It states the model, the invariants, the hardware-state
obligations, and the trust boundary. It is not itself a proof and not a paper.

---

## 0. The object being verified, and what "correct" means

Two quantities that mainstream systems conflate are here kept distinct:

- **Kernel allocation unit (KAU)**, size `P` — the smallest chunk of physical
  memory the allocator hands out, indexes in the page cache, and reclaims as a
  whole.
- **Minimum mapping granularity (MMG)**, size `M` — the smallest region the MMU
  can describe with one translation (the smallest hardware page / TLB entry).

Tessera sets `P = c · M` for a power-of-two cluster factor `c ≥ 1`, and may map a
suitably aligned, uniformly-permissioned KAU (or a run of them) with a single
**superpage** TLB entry. Translation state — presence, protection, dirty,
referenced — is tracked per-`M` in a **vector of `c` page-table entries** per
allocation unit. User space sees page size `M`; the kernel allocates and reclaims
in units of `P`.

**Correctness means ABI-preservation, stated as a refinement:** the
virtual-to-physical-and-permission behavior an application observes is *exactly*
that of a simple per-`M` mapping, regardless of whether a region is currently
mapped as a superpage, as individual `M`-sized entries within a KAU, or is
partially populated. Clustering and superpaging must be **invisible to
correctness**. That single sentence is the top-level theorem the whole effort
builds toward.

A second, equally load-bearing demand (see §4): an operation is correct only if
it brings the **hardware translation and cache state** to a configuration that
faithfully implements the new abstract state. Updating the abstract mapping is
not enough; the operation must also discharge the TLB and cache maintenance the
new state requires. A forgotten flush must be a **provable error**, not an
invisible one.

---

## 1. Governing philosophy: each milestone is complete in itself

This work is being undertaken under bounded time and resources. Structure it so
that **every milestone is a standalone result that retains its value even if no
further milestone is ever reached** — never a down-payment that is worthless
until the next instalment lands. The milestone breakdown in §8 is designed this
way deliberately. Prefer depth-first completion of one milestone to breadth-first
partial progress on several. If forced to stop, the project should end on a
finished, citable result, not a scaffold.

A corollary: write the *model and the invariants* down completely and early, even
before proving much. The model is the part that needs the author's judgment and
is hardest to reconstruct; the proof-grinding that follows is comparatively
mechanical and is the part most readily continued by another agent or person.
Front-load the irreplaceable part.

---

## 2. The model stack: three layers, each refining the one above

Do not model "the VMM" as one object. Build a tower and prove each layer
implements the one above (refinement). Each proof step bridges *one* level of
abstraction, never the whole gap at once.

**Layer S — Specification (what it means).** Memory as a partial function from
virtual address to `(physical address, permissions)` — equivalently, a per-`M`
mapping with a permission check. *No clustering, no superpages, no PTE vectors
appear here.* This layer is deliberately trivial; it encodes the ABI ("a load
from a mapped readable address returns the last value stored; a write to a
read-only address faults"). Its simplicity is the point — it is the promise,
stated so plainly a skeptic agrees it is what correctness means.

**Layer A — Algorithm (the design as pure data).** Memory as a set of
**extents**, each an aligned power-of-two run with uniform permissions; KAUs of
size `P`; an extent mapped either as a superpage or as a vector of `M`-grained
entries; COW sharing as a relation between extents and address spaces. The
operations — map, unmap, split, merge, promote, demote, COW-break — are **pure
functions** over this data. *The central theorem of the project lives here:* that
the extent/superpage representation, in any well-formed state, presents the same
behavior as Layer S. This is where most real correctness content sits, and it is
ordinary reasoning (case analysis, structural induction) over pure structures.

**Layer I — Implementation (the concrete representation).** Extents become the
actual data structure (a trie or B+-tree); PTE vectors become arrays of concrete
PTE bit-encodings; the sharing relation becomes reference-counted sharing-group
objects. This is where imperative code and Hoare/separation-logic reasoning enter
*if and when* the proof is pushed down to real code. It refines Layer A.

The discipline this buys: every aspect of the system attaches to exactly one
layer, and you never reason about an aspect where it does not belong.

---

## 3. The state and the invariants

The modeled machine state at Layers A/I includes, explicitly:

- the **abstract mapping** (Layer S object, for the refinement relation);
- the **extent set** / page-table representation;
- the **TLB**, as an explicit set of cached `(virtual range → physical,
  permissions)` entries — *this is not optional; see §4*;
- if cache-correctness is in scope, a **cache-state** representation keyed the way
  the target cache is indexed (virtual for VIVT, virtual-index/physical-tag for
  VIPT — the indexing scheme determines the maintenance obligation, so it is a
  parameter of the model, not a triviality).

**Well-formedness invariants** (each operation must preserve all of them):

1. **Disjoint, aligned extents.** Extents do not overlap; each is aligned to its
   size; sizes are powers of two times `M`.
2. **KAU integrity.** Allocation units are `P`-sized and `P`-aligned; the `c`
   PTE-vector slots of a KAU correspond to its `c` constituent `M`-pages.
3. **Superpage uniformity.** An extent is mapped as a superpage *only if* all its
   constituent `M`-pages are present with identical permissions. (Promotion
   precondition; demotion is forced the instant this would be violated.)
4. **Consistent split/merge.** Splitting an extent yields a set of sub-extents
   whose union is the original, with preserved alignment and non-overlap; merging
   is its sound inverse, permitted only for adjacent, identically-permissioned,
   same-backing extents.
5. **Dirty/referenced aggregation.** The per-KAU dirty/referenced answer is the
   correct aggregation (logical OR) of the per-`M` bits in the PTE vector.
6. **COW consistency.** A COW break leaves the sharing-group metadata and the
   page-table/PTE-vector state mutually consistent; reference counts reflect
   actual sharing.
7. **TLB coherence.** `TLB ⊆ current mapping`: no cached translation contradicts
   the current page tables. (The keystone invariant — see §4.)
8. **Cache coherence** (if in scope): no cache line holds data for a virtual
   address whose mapping has been removed or changed in a way the cache's
   indexing makes observable.

**A required modeling decision for COW-with-superpages.** Where the design takes a
simplifying assumption (e.g. "a COW write to any `M`-page of a superpage-mapped
extent demotes the whole extent before copying"), encode that assumption as an
**explicit precondition** of the operation and prove the operation sound *under
it*, rather than leaving it implicit. The act of stating the precondition
precisely is where the subtle design bugs surface; do not let a simplifying
assumption hide.

---

## 4. The hardware-state obligations — the crux

This section is the heart of the brief and the place where naïve data-structure
verification would let a catastrophic, classic VM bug slip through. Read it
carefully.

An operation that changes a mapping is **not correct merely because it updates the
abstract mapping and the extent set.** It is correct only if it *also* brings the
TLB and (where in scope) the caches to a state coherent with the new mapping.
`unmap` is the canonical case: removing the extent from the abstract mapping while
forgetting to invalidate the stale TLB entries leaves the real machine
translating a freed address through a stale entry — a use-after-free the
application can exploit. A model that omits the TLB **cannot see this bug**; a
pure-data proof would pass while the machine is unsound.

Therefore the TLB (and cache) state is part of what the proof reasons about, and
the obligation splits into two properties at very different difficulty levels:

**Property 1 — sequential coherence obligation (IN SCOPE; model this).** Each
operation's postcondition includes re-establishing invariants 7 (and 8): after
the operation, no TLB entry caches a translation that the new page tables
contradict, and no cache line holds stale data the indexing makes observable. The
operation's *steps must include the invalidation/maintenance* that achieves this,
and the proof discharges it. Concretely, `unmap(r)`'s theorem reads: after
`unmap(r)`, region `r` is absent from the abstract mapping **and** no TLB entry
covers `r` **and** (for VIVT) no cache line holds data for `r`'s virtual
addresses. An `unmap` lacking its flush **fails this theorem** — which is exactly
the desired outcome. This is *sequential* reasoning over a richer state (the
state has a TLB component); the invariant `TLB ⊆ current mapping` is what converts
a forgotten flush from an invisible bug into a provable one. This needs no
weak-memory machinery and **must be in the model from the start.**

**Property 2 — concurrent ordering of observation (OUT OF SCOPE initially; see
§5, §6).** On a multiprocessor, when one core unmaps and flushes its own TLB,
other cores may still hold stale entries until a shootdown IPI is sent and
acknowledged, and the *ordering* of the page-table write, the local flush, the
IPI, and remote accesses is governed by the relaxed hardware memory model. This —
the soundness of the shootdown *protocol* under weak memory — is the research-grade
part. It is a *different* property from "did the operation invalidate at all,"
and it is deliberately deferred. Do not conflate the two: Property 1 (the
obligation to invalidate) is sequential and in scope; Property 2 (how other cores
come to observe that invalidation) is concurrent and deferred.

The single most important instruction in this brief: **model the TLB as explicit
state and make a missing flush a provable error.** Everything else is detail.

---

## 5. The trust line — drawn explicitly

State these boundaries in the development itself, as named assumptions, exactly as
seL4 documents its trusted assembly:

- **Modeled and proved (sequential):** Layers S and A in full; the refinement
  S ⟸ A; all eight invariants including the TLB/cache coherence obligations of
  Property 1; the COW/demotion preconditions made explicit.
- **Checked in isolation, not in-situ (deferred):** the TLB-shootdown protocol's
  soundness under relaxed memory (Property 2) — to be addressed, if at all, as a
  standalone litmus-style check against an architecture memory model (herd/litmus),
  not as part of the main VMM proof.
- **Trusted, not proved:** the hardware behaves as the abstract translation model
  says (the MMU walks page tables thus; invalidation instructions have the stated
  effect; the cache's indexing is as modeled). The hardware model *is* an
  assumption; the whole proof is conditional on it. This is the honest boundary of
  all formal verification, not a gap to apologize for.
- **Deferred to Layer I:** the concrete data-structure implementation and its
  refinement of Layer A; the imperative code and its Hoare/separation-logic proof.

A coherent sequential proof of Layers S/A with Property-1 coherence obligations,
plus an explicit trusted boundary for Property 2 and the hardware model, is a
**complete and honest result in itself** — it mirrors where seL4 itself drew many
of its lines.

---

## 6. Deliberately out of scope (so the scope stays finishable)

- Concurrent weak-memory ordering / barrier placement (Property 2) — deferred to
  isolated litmus checks or left trusted.
- Interrupt reentrancy beyond the assumption of non-preemptible critical sections
  (or, if modeled, treated as a concurrent agent — but not initially).
- The hardware memory model itself and cache-coherence-protocol internals —
  trusted.
- The imperative implementation — deferred to Layer I.

Resist scope creep into these; they are where the effort becomes unbounded, and
the sequential algorithm result is valuable without them.

---

## 7. Logic and prover orientation

**Named logics, in the order you will meet them:**

- **Separation logic** (Reynolds, O'Hearn) — sequential reasoning about mutable
  heap and pointers with local, composable assertions. The bedrock for Layer I.
- **Concurrent separation logic / rely–guarantee** (O'Hearn; Jones; fused as
  RGSep) — concurrency under a sequentially-consistent memory model. The shootdown
  protocol, *if* tackled, is naturally a rely–guarantee contract.
- **Iris** — higher-order concurrent separation logic framework (in Coq); the
  modern center of gravity for concurrent verification, including weak-memory
  extensions.
- **Relaxed/weak-memory logics** — the ARM/x86 axiomatic & operational models
  (Cambridge lineage) with the **herd/litmus** toolchain; relaxed separation
  logics (RSL, FSL, GPS) and weak-memory Iris. The barrier layer (Property 2).
- **Relaxed virtual memory** — the frontier: weak-memory models extended to
  include the TLB, the page-table walk, and maintenance/invalidation instructions
  as first-class participants. This is exactly the formal home of Property 2 for
  address translation; consult it only if the concurrent layer becomes a goal.
- Caches (VIVT/VIPT) have no separate named logic — handled either as Property-1
  sequential coherence obligations (here) or folded into the relaxed-virtual-memory
  models. Reentrancy likewise is modeled as concurrency, not a logic of its own.

**Prover decision rule:**

- The sequential milestones (M1–M3 below, the achievable core) need only ordinary
  higher-order logic with good support for inductive types and refinement. **Use
  the prover you will actually finish in.** If a prover is already installed in
  this shell, use it. Absent a forcing constraint, **Lean4 (with mathlib)** or
  **Isabelle/HOL** are both excellent for this layer; Isabelle has the seL4
  precedent and strong automation, Lean4 has modern ergonomics and superb
  inductive/algebraic support. Either suffices for everything sequential.
- **Only if the concurrent layer (Property 2) becomes a committed goal** should
  prover choice bend toward **Coq**, because Iris, CompCert, CertiKOS, and the
  relaxed-virtual-memory work live there and largely nowhere else to the same
  maturity. Know this in advance so a tower is not built that must later be
  rebuilt.
- Pragmatic principle: the prover is a tool subordinate to momentum and to
  infrastructure availability. If a crucial tool forces a choice, follow it.

For the work this brief actually targets, pick the comfortable prover and proceed;
do not let prover-shopping delay the first proof.

---

## 8. The milestones (each complete in itself)

**M1 — One operation preserves one invariant.** Define the extent and the
well-formedness predicate (invariants 1–2); define `split`; prove `split`
preserves well-formedness. Pure data, structural induction, no TLB yet. *Why it
stands alone:* it establishes the core data model and demonstrates the whole
technique in miniature; it is a real, citable result and the foundation everything
else reuses.

**M2 — All operations preserve all invariants, including the coherence
obligation.** Extend to map, unmap, merge, promote, demote, COW-break; bring the
**TLB into the state** and add invariant 7 (and 8 if in scope); prove every
operation preserves every invariant, *including* re-establishing TLB/cache
coherence — so that, e.g., an `unmap` without its flush fails to verify. *Why it
stands alone:* this is the result that says "the clustered VMM maintains a
self-consistent, hardware-coherent state under every operation," which is
independently meaningful and is the first result that takes the §4 hardware
obligation seriously.

**M3 — The refinement theorem (ABI-preservation).** Prove that the Layer-A
extent/superpage representation, in any well-formed state, refines the Layer-S
per-`M` mapping: clustering and superpaging are invisible to the
virtual-to-physical-and-permission behavior. *Why it stands alone:* this is the
headline correctness statement — the formal version of "the ABI cannot tell
whether a region is superpage-mapped, individually mapped, or partially
populated." Reaching M3 is the project's central claim proved.

(Beyond M3, optional and separate: Layer-I refinement to concrete data structures
and imperative code; and the Property-2 concurrent shootdown check via
herd/litmus. Neither is required for M1–M3 to be a complete result.)

---

## 9. The first session, concretely

Do not start at the mountain. Start here:

1. Choose the prover (or use the installed one) per §7; do not deliberate long.
2. Define the **extent** type: `(base, size, permissions)` with `size` a power of
   two times `M`, `base` aligned to `size`.
3. Define **well-formedness** of an extent set: pairwise non-overlap, each extent
   aligned, sizes valid (invariants 1–2).
4. Define **`split`**: an extent into a list/set of sub-extents tiling it.
5. Prove **`split` preserves well-formedness** (M1).

That single proof teaches more about whether this approach and prover suit the
project than any amount of further reading, and it is already a genuine result.
Expand outward within Layer A from there, following §8.

---

## 10. Nomenclature (avoid the overloaded word)

Throughout the development, prefer **"kernel allocation unit"** (`P`) and
**"minimum mapping granularity"** (`M`) over the word "page," which conflates the
two and is the source of most confusion in this domain — for human readers and for
the model alike. Reserve "superpage" for a single large TLB entry spanning one or
more KAUs. Keep "the TLB is a *cache* of the translation function" as the mental
model for §4: the operation's job is to keep that cache coherent with the page
tables, and the proof's job is to make any failure to do so visible.

---

*End of brief. The first deliverable is M1: `split` preserves well-formedness.
Begin there.*

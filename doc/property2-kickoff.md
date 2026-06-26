# Property 2 — concurrent TLB-shootdown soundness: kickoff

The sequential proof (`RESULTS.md`) discharged **Property 1**: each operation's steps
include the TLB/cache maintenance, and a forgotten flush is a provable error. This
brief opens **Property 2** (kickoff §4): *how other cores come to observe that
invalidation* — the soundness of the **TLB-shootdown protocol under relaxed memory**.
It is a different property from "did the operation invalidate at all," and it is the
research-grade frontier the brief (§5–§7) routes to a standalone check and to Coq/Iris.

## The object

On a multiprocessor, `unmap(r)` on core 0:

1. writes the page table to remove `r` (break-before-make: write *invalid* first);
2. invalidates its **own** TLB (`TLBI`), with barriers (`DSB`, `ISB`);
3. sends a **shootdown IPI** to the other cores;
4. each remote core invalidates its TLB and **acknowledges**;
5. core 0 waits for all acks before treating the page as free (and reusing the frame).

The hazard: between (1) and a remote core completing (4), that remote core may still
hold — or **speculatively re-walk into** — a *stale* translation, and access the freed
frame: a cross-core use-after-free. Soundness is that **no remote core can translate
through `r` after the protocol completes**, given the architecture's relaxed-memory
ordering of the page-table write, the `TLBI`s, the barriers, the IPI, and the remote
accesses. The TLB is a hidden cache the hardware fills by *walking* the page table,
possibly speculatively; this is what makes it weak-memory-subtle and distinct from
ordinary message passing.

## Scope, and the two complementary routes (kickoff §5, §7)

**In scope:** the ordering/observation soundness of the shootdown *protocol* against an
**architecture memory model that includes the TLB and the page-table walk** as
first-class participants — the *relaxed virtual memory* frontier (kickoff §7). Out of
scope: re-deriving the hardware memory model itself (trusted); interrupt-handler
internals beyond the IPI's ordering effect.

**Route A — litmus check (the brief's "if at all" baseline; tooling ready).**
`herd7` 7.58 is installed and supports **`-variant vmsa`** — the Armv8-A VMSA model with
`[PTE(x)]=(oa:PA(x),valid:…)` descriptors, `TLBI VAE1IS`, `DSB ISH`, `ISB`. So the
shootdown's ordering can be encoded as **litmus tests checked against the official Arm
axiomatic model**, exactly the "standalone litmus-style check" §5 names. The discipline:
for each test, show the stale-translation outcome is **forbidden with the barriers/TLBI
present** and **allowed without them** — proving the maintenance is *necessary*, the
concurrent analogue of `unmap_without_flush_breaks_coherence`. Artifacts live in
`property2/litmus/`.

**Route B — Iris protocol proof (the committed Coq + Iris track).** Model the shootdown
as a concurrent protocol with shared state (page table, per-core TLBs as explicit
state, the IPI channel) and prove it re-establishes coherence (`TLB ⊆ mapping` on every
core after completion) — the concurrent analogue of `unmap_correct`. Paced: first under
**sequential consistency** (a rely–guarantee / Iris-invariant proof of the *protocol
logic*), then under a **weak-memory** base. Coq 8.20 + `coq-iris` (installing). Artifacts
in `property2/coq/`.

The two routes are complementary, not redundant: Route A checks that the *Arm model*
permits no stale read for concrete shapes; Route B proves the *protocol logic* sound for
an arbitrary number of cores. Route A is the immediate, runnable evidence; Route B is
the general theorem.

## Milestones (each standalone, as in the sequential layer)

- **P2.0 — environment.** ✅ **Complete, both routes live.** herd7 7.58 VMSA confirmed
  (models `TLBI`, PTE writes, faults); `coq-iris` 4.4.0 + `coq-stdpp` 1.12 installed and
  verified (`property2/coq/HelloIris.v` — separation-logic proofs compile).
- **P2.1 — the core shootdown litmus.** ✅ **Done** (`property2/litmus/shootdown-mp.litmus`):
  P0 invalidates `PTE(x)` + `TLBI VMALLE1IS` + barriers + signals a flag; a remote P1
  that observes the flag **provably cannot** read `x` through a stale translation
  (`Never`, vs `Sometimes` for the `noTLBI` control). The architectural analogue of
  `unmap_without_flush_breaks_coherence`. See `property2/README.md`.
- **P2.2 — the necessity family.** ✅ **Done** (`property2/litmus/`): with the full
  shootdown the stale read is `Never`; dropping the `TLBI` (`shootdown-mp-noTLBI`), P0's
  completion `DSB` (`shootdown-noP0dsb`), or P1's read `DSB`+`ISB` (`shootdown-noP1bar`)
  each makes it `Sometimes` — every step is load-bearing against the Arm model. (Open
  refinements: by-VA `VAE1IS` operand; break-before-make *ordering*; speculative walk.)
- **P2.3 — Iris SC protocol.** ✅ **Done** (`property2/coq/`). **P2.3a** (`mp.v`): the
  message-passing skeleton — P0 does the page-table write then raises the completion flag;
  the remote waits then reads, *proven* to observe the write (`mp_spec`, one-shot-token
  invariant). **P2.3b** (`tlb_shootdown.v`): an *explicit per-core TLB* — the remote holds
  a (stale-able) cached translation; `unmap` invalidates the PTE, **invalidates the TLB**,
  then signals; `shootdown_spec` proves the remote re-walks the now-invalid PTE and
  observes the unmapped state (`false`) rather than the stale cache. The concurrent
  analogue of `unmap_correct`; the proof relies on the TLB-invalidation step (drop it and
  the reader can no longer be shown to read `false`).
- **P2.4 — weak-memory.** ✅ **Done** (`property2/coq/weak/`): P2.3 lifted onto
  **iRC11/gpfsl** (Iris over the ORC11 release/acquire relaxed-memory model), in a
  dedicated `wm` opam switch (coq 8.20.1 + `coq-gpfsl` dev.2025-11-18 + `rocq-iris`-dev)
  so the stable `surd` switch stays intact. Two proofs, both `Qed` and **axiom-free**
  (`Print Assumptions` = *Closed under the global context*):
  **P2.4a** `mp_weak.v` (`shootdown_mp_gen_inv`) — weak-memory MP: the remote's acquire
  of the released flag provably observes the page-table write (`42`) over ORC11;
  **P2.4b** `tlb_shootdown_weak.v` (`shootdown_reclaim_gen_inv`) — the *reclaim* variant:
  the frame is freed after the protocol, proven race-free because the acquire
  synchronised (the cross-core use-after-free, under relaxed memory). The release/acquire
  pair is the proof-side image of the litmus necessity family — make either access
  *relaxed* and the happens-before edge, hence the proof, vanishes, mirroring
  `shootdown-noP0dsb`/`noP1bar` going `Sometimes`. These re-derive gpfsl's own verified
  MP examples under the shootdown reading; the frontier reached.

## Trust boundary

- **Established by Route A:** the Arm axiomatic VMSA model (as implemented by herd7)
  admits no stale translation for the tested shapes when the protocol's barriers/TLBIs
  are present — and does admit it when they are removed. *Trusts:* herd7's faithfulness
  to the architecture, and that the tested shapes are representative.
- **Established by Route B:** the protocol logic is sound for all core counts.
  *Trusts:* the memory model the Iris instance is built over.
- **Still trusted:** the hardware honours the architecture model; `TLBI`/`DSB`/`ISB`
  have their stated effects. This is the same honest boundary as the sequential layer
  (kickoff §5), now drawn one level deeper (the *ordering* of maintenance, not just its
  presence).

Property 1 (proved: the operation *must* invalidate) plus Property 2 (the remotes
*come to observe* the invalidation) together are the full hardware-coherence story for
the clustered VMM.

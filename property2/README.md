# Property 2 — TLB-shootdown soundness (work area)

Opening the concurrent layer the sequential proof deferred. See
[`../doc/property2-kickoff.md`](../doc/property2-kickoff.md) for scope and the two
routes. Status: **both routes substantially complete** — Route A (litmus) has the sound
protocols + the full necessity family (P2.1–P2.2); Route B (Coq + Iris) has the SC
protocol proofs (P2.3a/b) **and** the weak-memory iRC11 proofs (P2.4a/b), all axiom-free.

## Route A — litmus checks against the Armv8-A VMSA model (`litmus/`)

Tooling: **`herd7` 7.58 with `-variant vmsa`** — the Arm Virtual Memory System
Architecture model, with page-table descriptors (`[PTE(x)]=(oa:PA(x),valid:…)`),
in-program PTE writes (storing a *typed descriptor*, not a register zero), `TLBI`,
`DSB`, `ISB`, and translation faults as first-class events.

Run: `cd litmus && ./run.sh` (or `herd7 -variant vmsa <test>.litmus`).

**Sound protocols** (forbidden = no remote stale read):

| Test | Shape | Stale read |
|------|-------|:--:|
| `shootdown-mp.litmus` | **cross-core** MP: P0 unmaps + `TLBI VMALLE1IS` + signal; remote P1 reads after seeing the signal | **`Never`** |
| `bbm-tlbi.litmus` | single-core break-before-make: invalidate PTE + `TLBI` + `DSB` + `ISB` | **`Never`** |

**Necessity family** — drop one ingredient, the stale read returns (each step is
load-bearing):

| Test | drops | Stale read |
|------|-------|:--:|
| `shootdown-mp-noTLBI.litmus` | the `TLBI` | **`Sometimes`** |
| `shootdown-noP0dsb.litmus` | P0's `DSB` ordering TLBI-completion before the signal | **`Sometimes`** |
| `shootdown-noP1bar.litmus` | P1's `DSB`+`ISB` ordering the read after the signal | **`Sometimes`** |
| `bbm-notlbi.litmus` | the `TLBI` (single-core) | **`Sometimes`** |

The pair `shootdown-mp` (Never) vs each necessity variant (Sometimes) is the
**architectural analogue of `unmap_without_flush_breaks_coherence`** — *with* the full
shootdown the Arm relaxed-memory model forbids the cross-core use-after-free; drop the
`TLBI`, P0's completion barrier, *or* P1's read barrier and the model admits it.

### Caveats / open refinements

- **`VMALLE1IS` (invalidate-all, Inner-Shareable broadcast)** is used — a coarse but
  real shootdown (full-ASID flushes do occur, and IS broadcasts to remote TLBs). The
  finer **`TLBI VAE1IS, Xt` (by-VA)** did *not* forbid the stale read with either the VA
  (`x`) or `PTE(x)` operand; herd's by-VA address-matching has a subtlety (the
  page-number/ASID encoding, or a model condition) that needs deeper VMSA expertise. A
  noted refinement — it would make the shootdown *targeted* rather than global.
- The check is against **herd7's VMSA model**; faithfulness to silicon is the standing
  trusted-hardware assumption (kickoff §5).
- **Status: P2.1 + P2.2 done** (sound protocols + the full necessity family above).
  Remaining Route-A refinements: by-VA `VAE1IS`; the break-before-make *ordering* test
  (TLBI before vs after the PTE write); the speculative-walk shape.

## Route B — Iris protocol proof (`coq/`)

**Ready.** `coq-iris` 4.4.0 + `coq-stdpp` 1.12 installed (opam switch `surd`); verified
by `coq/HelloIris.v` (`coqc HelloIris.v` after `eval $(opam env --switch=surd)`).

A concurrent model of the shootdown (page table, per-core TLBs, IPI) proving it
re-establishes `TLB ⊆ mapping` on every core — the concurrent analogue of
`unmap_correct`. Build: `eval $(opam env --switch=surd); coqc coq/mp.v`. Paced:
- **P2.3a** — ✅ **done** (`coq/mp.v`): the SC *message-passing skeleton* in Iris
  HeapLang. P0 does the page-table write (`x := 37`) then signals (`y := 1`); the remote
  thread waits for the signal then reads `x`, and `mp_spec` *proves* it observes the
  write (37). A one-shot exclusive-token invariant transfers the data across the flag.
  The ordering core the TLB layer hangs on; `wait_spec` + `mp_spec`, both `Qed`.
- **P2.3b** — ✅ **done** (`coq/tlb_shootdown.v`): an explicit per-core TLB. The remote
  holds a cached translation (`tlb`, initially valid → stale-able); `unmap` does
  `pte := false ;; tlb := false (* shootdown *) ;; flag := true`; `shootdown_spec` proves
  the remote, after the flag, re-walks the now-invalid PTE and reads the unmapped state
  (`false`) — not the stale cache. The concurrent analogue of `unmap_correct`; the proof
  hinges on the `tlb := false` step (the invalidate-before-use discipline). The litmus
  side (above) exhibits the stale read directly when the invalidation is dropped.
- **P2.4** — ✅ **done** (`coq/weak/`), the genuine weak-memory frontier, over
  **iRC11/gpfsl** (Iris on the ORC11 release/acquire relaxed-memory model) in a dedicated
  `wm` opam switch (so the stable `surd` 4.4.0 setup stays intact). Two proofs, both
  `Qed` and **axiom-free** (`Print Assumptions` = *Closed under the global context*):
  - **P2.4a** (`mp_weak.v`): weak-memory message passing — the writer releases the flag,
    the remote acquires it, and the read provably observes the page-table write (`42`)
    over ORC11. The release/acquire pair *is* the litmus necessity family's `DSB`/`ISB`
    (drop it → relaxed access → no happens-before → underivable, the proof-side twin of
    `shootdown-noP0dsb`/`noP1bar` going `Sometimes`).
  - **P2.4b** (`tlb_shootdown_weak.v`): the **reclaim** variant — after the protocol the
    unmapping core *frees the frame* (`delete`); the proof shows the free is race-free
    *because* the acquire synchronised (full ownership recovered via view-token
    cancellation). The cross-core use-after-free, closed under relaxed memory.

  These re-derive gpfsl's own verified MP examples (`gpfsl-examples/mp/`) under the
  shootdown reading; the contribution is the framing, the cross-route correspondence, and
  the reclaim shape (see `coq/weak/README.md`). Build: `cd coq/weak && ./build.sh`.

Build the SC Iris proofs: `cd coq && ./build.sh`. Build the weak-memory proofs:
`cd coq/weak && ./build.sh`.

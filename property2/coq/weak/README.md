# P2.4 — the shootdown ordering under a genuine weak-memory base (iRC11)

This lifts the SC protocol proofs (`../mp.v` = P2.3a, `../tlb_shootdown.v` = P2.3b)
off sequential consistency and onto a **real relaxed-memory model**, closing the gap
the kickoff named as the frontier (`doc/property2-kickoff.md` P2.4). Where Route A
(litmus) checks the *Arm* model for concrete shapes and the SC Iris proofs assume an
SC base, this proves the *protocol logic* sound over **release/acquire relaxed memory**
for an arbitrary scheduler.

## Tooling — gpfsl / iRC11 (separate `wm` switch)

[iRC11](https://gitlab.mpi-sws.org/iris/gpfsl) is Iris instantiated over **ORC11** (the
operational *promising semantics without promises* — release/acquire, relaxed, and
non-atomic accesses, with per-thread *views*). gpfsl = GPS + FSL in that base. It is the
most established general weak-memory separation logic, and reuses all of Iris.

Installed in a **dedicated opam switch `wm`** (coq 8.20.1 + iris-dev + `coq-orc11` +
`coq-gpfsl`) so the stable `surd` switch (iris 4.4.0, the SC proofs) stays intact, per
the kickoff's "separate switch" note. Build: `eval $(opam env --switch=wm)` then `./build.sh`.

## The correspondence that makes this the right model

The litmus necessity family (`../../litmus/`, P2.2) showed *which* barriers are
load-bearing on Arm. iRC11 names the **same** barriers as access modes — so the proof
and the litmus check the same fact from two sides:

| shootdown step (Arm) | litmus necessity test | iRC11 counterpart |
|---|---|---|
| P0: `DSB` after `TLBI`, before raising the flag | `shootdown-noP0dsb` → `Sometimes` | **release** store of the flag (`<-ʳᵉˡ`) |
| P1: `DSB`+`ISB` after seeing the flag, before the access | `shootdown-noP1bar` → `Sometimes` | **acquire** load of the flag (`!ᵃᶜ`) |
| the data/PTE write ordered before the signal | (carried by the above) | non-atomic write, released by the flag |

The release/acquire pair is exactly what creates the **happens-before** edge from P0's
page-table write to P1's access. Drop it — use a *relaxed* flag access — and the edge is
gone: the reader is no longer guaranteed to see the write, the proof becomes
**underivable**, and ORC11 admits the stale read. That underivability is the proof-side
twin of `shootdown-noP0dsb`/`noP1bar` going `Sometimes`, and of the SC result
`unmap_without_flush_breaks_coherence`.

## Files (paced like the SC track)

- **`mp_weak.v` (P2.4a)** — weak-memory message passing. Writer: `data := 42` then
  `flag <-ʳᵉˡ 1`; reader: `repeat: !ᵃᶜ flag` then `!data`; proven to read `42` over
  ORC11. The relaxed-memory analogue of `../mp.v`. Modelled on gpfsl's own
  `gpfsl-examples/mp/` (`proof_gen_inv.v`, general-invariant style — the closest match to
  our SC invariant idiom).
- **`tlb_shootdown_weak.v` (P2.4b)** — the **reclaim** variant: after the protocol the
  unmapper *frees and could reuse the frame* (`delete`). This is the cross-core
  use-after-free directly: the remote, synchronised by the acquire, never touches the
  freed frame through a stale view. Modelled on gpfsl's `mp/proof_reclaim_gps.v` /
  `view_inv` cancellation.

## Trust boundary (one level deeper than the SC proofs)

Establishes the protocol sound over ORC11's relaxed semantics — no longer assuming an SC
base. Still trusts: ORC11's faithfulness to the hardware model, and that the access modes
(`rel`/`acq`) are discharged by the architecture's `DSB`/`ISB` (which Route A checks on
the Arm side). The two routes meet here: the litmus shows Arm honours the barriers; iRC11
shows the barriers suffice for the protocol.

## Status — ✅ done, both proofs axiom-free

Built in the `wm` switch (coq 8.20.1 + `coq-gpfsl` dev.2025-11-18 over `rocq-iris`-dev):

| file | theorem | result |
|---|---|---|
| `mp_weak.v` (P2.4a) | `shootdown_mp_gen_inv` | `Qed`, `Print Assumptions` = **Closed under the global context** |
| `tlb_shootdown_weak.v` (P2.4b) | `shootdown_reclaim_gen_inv` | `Qed`, `Print Assumptions` = **Closed under the global context** |

Run: `./build.sh` (or `eval $(opam env --switch=wm); coqc -Q . "" mp_weak.v`).

**Provenance, honestly.** The programs are gpfsl's own message-passing examples
(`gpfsl-examples/mp/code.v`: `mp` and `mp_reclaim`) and the proofs are gpfsl's
`mp_instance_gen_inv` / `mp_instance_reclaim_gen_inv` (`proof_gen_inv.v`), re-derived
here under the shootdown reading with our naming. The one-shot token (`uniq_token.v`) is
vendored verbatim because gpfsl's `examples` are not installed to the load path. The
Tessera contribution is **not** the Iris proof engineering — it is (i) establishing that
the *VM shootdown's* ordering core is exactly an instance gpfsl already verifies, (ii)
the cross-route correspondence to the litmus necessity family (the release/acquire ARE
the `DSB`/`ISB`), and (iii) carrying it to the **reclaim** shape, which is the cross-core
use-after-free the property exists to rule out — now closed over a genuine relaxed-memory
model, axiom-free.

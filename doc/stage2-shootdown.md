# Tessera — Stage 2: the N-core TLB-shootdown over the concrete machine

**Goal.** Prove, over the *generated* Sv39 machine (`hardware/rocq/machine.v`), that
the broadcast TLB-shootdown re-establishes coherence on every core — "no core
translates a freed frame after the protocol completes" — with the concrete
`translate` / `tlb_lookup` / `sfence_vma_va` as the participants, not booleans.

This is the concurrent layer the sequential proof (Stage 1/1.1) deferred: Stage 1
proved that *one* core's unmap+flush faults and that a flush-less unmap leaves a
stale entry (the §4 crux); Stage 2 proves the remotes *come to observe* the
invalidation (kickoff Property 2).

## The object (kickoff property2-kickoff.md)

On a multiprocessor, `unmap(va)` on core 0:

1. writes the page table to remove `va` (break-before-make: write invalid first);
2. invalidates its **own** TLB;
3. sends a shootdown IPI to the other cores;
4. each remote core invalidates its TLB and **acknowledges**;
5. core 0 waits for all acks before treating the frame as free (and reusing it).

Soundness: no core translates through `va` after the protocol completes.

## Decisions (2026-08-13)

- **N-core broadcast** (not just two-core MP): the theorem is *for all cores* in the
  concrete `Machine`.
- **HeapLang + concrete values**: the program stores the actual `Pte`/`TlbEntry`
  (integer-encoded) in heap locations; the unmap literally writes the invalid PTE and
  clears each TLB.
- **Rocq 9.2 switch** (`rocq-iris 4.5.0` + `rocq-iris-heap-lang`), compiling against
  the generated model. (The old P2.3b proof lives in the `surd` switch; this is the
  new spine's home.)

## Pacing (each standalone)

- **S2.0 — pure/sequential.** `hardware/rocq/shootdown.v`: `shootdown m root va` =
  remove the leaf PTE + `sfence_vma_va` every core, and `shootdown_correct`: assuming
  all cores share `satp_ppn = root`, every core has `translate = None ∧ tlb_lookup =
  None`. Pure, axiom-free, reuses Stage 1.1. This is the *target* property the
  concurrent proof must match.
- **S2.1 — concurrent SC (Iris HeapLang).** A broadcast program with the machine state
  in the heap (`pte ↦ Pte`, `tlb : N ↦ option TlbEntry`, `ack : N ↦ bool`, `go ↦
  bool`); a broadcast-barrier invariant (phase + ack counter via ghost `gset`);
  `broadcast_spec` reifies the post-state to the pure machine and cites
  `shootdown_correct`.
- **S2.2 — weak memory (gpfsl/ORC11).** The release/acquire lift, in the separate `wm`
  switch, mirroring P2.4a/b. Deferred.

## Concrete-value encoding (S2.1)

`Pte` (5 bools + 44-bit ppn) and `option TlbEntry` (27-bit vpn + 44-bit ppn + 2-bit
perm) are bit-packed into a `Z` and stored as `#z`. Encode/decode are inverses (proved
once); the invariant keeps the decoded value in the spec so the proof never does bit
arithmetic — the same "keep it opaque" discipline as Stage 1.

## The invariant (S2.1, draft)

    inv := ∃ (phase : bool),
      go ↦ #phase ∗ pte ↦ #invalid_pte ∗
      (if phase
       then all-acked (ack-counter = full set)       (* post: every TLB cleared *)
       else ∀ i, tlb[i] ↦ Some e_i ∧ ack[i] ↦ false) (* pre: every core stale-able *)

The PTE is invalid from the write onward, independent of `phase`; `phase` only
tracks the go/ack barrier. **S2.0→S2.1 bridge:** S2.1's postcondition must reify
the concurrent final heap state to *exactly* `shootdown m root va` (or the same
`Forall (translate = None ∧ tlb_lookup = None)` conclusion) so it cites
`shootdown_correct` directly.

with a ghost `gset` counter of acked cores; each remote adds itself on ack, and core 0
waits until the set is full before returning (the "free is safe" point).

## Trust line

- **Now proved:** the broadcast re-establishes coherence on every core, sequentially
  (S2.0) and under the concurrent schedule (S2.1), over the generated walk.
- **Still trusted:** the encoding of `mword` (SailStdpp); SC (S2.1) until S2.2 lifts it
  to ORC11; the IPI is modeled as a shared flag (its ordering effect, not its delivery).

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
- **S2.2 — weak memory (gpfsl/ORC11).** The release/acquire lift of the S2.1 broadcast
  onto a genuine relaxed-memory base, *over the generated `machine.v`* (not gpfsl's toy
  `mp` example). Now reconciled into the **rocq-9.2 switch** with the vendored dev stack
  (`third_party/{stdpp,iris,gpfsl}` — no separate `wm` switch). Design below.

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

## S2.1 — concrete design

### Value encoding (`shootdown_iris.v`, Rocq)

HeapLang's `val` is fixed, so the concrete `Pte`/`TlbEntry` are encoded as `val`:

- `encode_pte (p : Pte) : val` — nested `PairV` of the five bools plus `#(word_to_N
  p.ppn)` (the 44-bit PPN as a Z).
- `encode_tlb (o : option TlbEntry) : val` — `InjLV #()` for `None`; `InjRV` of a
  nested pair (27-bit vpn, 44-bit ppn, 2-bit perm) for `Some e`.
- `decode_pte : val → option Pte`, `decode_tlb : val → option (option TlbEntry)`, with
  `decode_pte (encode_pte p) = Some p` and dually — proved once by case analysis; no
  bit arithmetic (the fields are stored as-is, only the PPN/VPN go through
  `word_to_N`).

### Program (single VA `va`, N cores; HeapLang)

    broadcast n :=
      pte := ref (encode valid_leaf_pte);        (* the leaf PTE, initially mapped *)
      tlb := AllocN n (encode (Some e));         (* every core caches va (worst case) *)
      ack := AllocN n #false;                    (* per-core ack *)
      go  := ref #false;
      pte <- encode invalid_pte;                 (* step 1: break-before-make *)
      tlb[0] <- encode None;                     (* step 2: invalidate own TLB *)
      go <- #true;                               (* step 3: broadcast *)
      Fork remotes 1..n-1;                       (* step 4: each waits, clears, acks *)
      wait_all_acks ack n                        (* step 5: free-is-safe point *)

    remote i := wait go ;; tlb[i] <- encode None ;; ack[i] <- #true

### Invariant (broadcast barrier)

    inv := ∃ phase, go ↦ phase ∗ pte ↦ encode pte(phase) ∗
       (if phase
        then ghost-counter = acked set (each remote added itself after clearing)
        else (∀ i, tlb[i] ↦ encode (Some e_i)) ∧ (∀ i, ack[i] ↦ #false))

A ghost `gset` counter: each remote adds `i` on ack; core 0's `wait_all_acks` loops
until the set is full. The PTE is invalid from the write onward (independent of
`phase`).

### Theorem

    broadcast_spec : {{{ True }}} broadcast #n
      {{{ RET #(); pte ↦ encode invalid_pte ∗
          (∀ i, tlb[i] ↦ encode None) ∗ (∀ i, ack[i] ↦ #true) }}}.

Reify the post-state to a `Machine` (`mem = [leaf PTE invalid]`, `cores = map (λi.
{| satp := root; tlb := [] |}) [0..n)`) and cite `shootdown_correct` for the
`Forall (translate = None ∧ tlb_lookup = None)` conclusion.

### Proof strategy

1. Encode/decode inverses (pure case analysis).
2. `wait` spec + `wait_all_acks` spec (loop + counter).
3. The barrier invariant, then the unmapper and remote `wp_par`/`wp_fork` proofs.
4. Reification lemma (post-heap ⟶ `shootdown m root va`) → conclude via `shootdown_correct`.

## S2.2 — weak memory (gpfsl/ORC11)

### Toolchain (reconciled 2026-08-14)

The P2.4a/b weak proofs lived in a separate `wm` switch (coq 8.20.1 + gpfsl dev).
That split is gone: S2.2 runs in the **rocq-9.2** switch against vendored dev source,
all committed as submodules:

    third_party/stdpp  @ 9c7afbb6   (the exact dev commit dev iris pins)
    third_party/iris   @ fdc7d5868  (iris 4.5.0-237-g, the dev iris gpfsl master needs)
    third_party/gpfsl  @ 907eac66   (gpfsl master, rocq-9.2)

built in-tree and installed into `~/.opam/rocq-9.2/lib/coq/user-contrib` (originals
backed up to `*.bak.*`). Two drift fixes were required, committed in `02ce71b`:

- dev iris: `ghost_var`'s fraction is now `dfrac` (`DfracOwn 1`, not `1`).
- dev stdpp lowered `{[ x ]}` / `{[ k := a ]}` to level 0, clashing with Sail's
  level-1 `{[ r 'with' f := e ]}` record-update notation; `build.sh` moves the
  (unused) record-update notations to level 0 after Sail generation.

Smoke test `hardware/rocq/s2_smoke.v` confirms gpfsl and `machine_types.v`/`machine.v`
import side by side with no notation/instance clash — the reconciliation frontier.

### The release/acquire structure (weak-memory lift of S2.1)

Under ORC11, the S2.1 SC heap accesses become access-annotated. The barrier decomposes
into 2(N−1) message-passing instances — the same ordering core P2.4a/b proved for
`#42`, here carried by the *machine* values `encode_pte invalid_pte` / `encode_tlb None`:

    leader:  pte <- encode invalid_pte ;; go <-ʳᵉˡ true         (* release the PTE write *)
    remote i: repeat !ᵃᶜ go ;; tlb[i] <- encode None ;;
              ack[i] <-ʳᵉˡ true                                (* release the TLB clear *)
    leader:  !ᵃᶜ ack[i]  (for each i)                          (* acquire each ack *)

Each release/acquire pair creates the happens-before edge that makes the data write
visible; the leader's final `!ᵃᶜ ack[i]` for every `i` is the "free is safe" point.
Dropping any `ʳᵉˡ`/`ᵃᶜ` makes the corresponding happens-before edge underivable — the
proof-side twin of the litmus `Sometimes` cases and of
`unmap_without_flush_breaks_coherence`.

### Pacing

- **S2.2a — two-core over the machine.** ✅ `hardware/rocq/shootdown_weak.v`
  (`shootdown_weak_gen_inv`, axiom-free): the leader's `pte <- #(encode_pte invalid_pte)
  ;; go <-ʳᵉˡ #1` is observed by the remote's `repeat !ᵃᶜ go ;; !pte` — the release/acquire
  happens-before carries the *machine* PTE value (the gpfsl value model is
  `LitPoison | LitLoc | LitInt`, so the PTE is bit-packed into a `Z` here).  Combined
  with `invalid_pte_not_valid` this is "the remote sees the invalid entry".
- **S2.2b — remote→leader ack round-trip.** ✅ `hardware/rocq/shootdown_weak.v`
  (`shootdown_weak_ack_gen_inv`, axiom-free): the remote's `tlb <- #(encode_tlb None) ;;
  ack <-ʳᵉˡ #1` is observed by the leader's `repeat !ᵃᶜ ack ;; !tlb`, which returns
  `encode_tlb None` — i.e. the release/acquire carries "the TLB entry is cleared" back to
  the waiting leader.  This closes the remote→leader half of the S2.1 broadcast; the
  remaining step is to compose S2.2a + S2.2b into the N-core `wait_all_acks` barrier and
  reify to `invalidate_shootdown` (folded into S2.2c).
- **S2.2c — N-core broadcast (scaffold).** 🚧 `hardware/rocq/shootdown_weak_broadcast.v`
  compiles the scaffold: the program (leader writes invalid PTE, releases `go`, forks N
  remotes, waits on N single-writer `ack[i]` flags), the invariant (`go_released` + per-core
  `ack_cell`), the per-core `UTok`-disjunction ack buffer (S2.2b pattern), and the pure
  `bc_machine n i` reification (cores 0..i-1 cleared, cores i..n-1 stale, PTE invalid).
  Key design point: the machine ghost is held by the leader *outside* the invariant and
  advanced in lockstep with ack acquisition — no auth-frag pending-map bookkeeping is
  needed (unlike S2.1's counter), because the leader iterates `i = 0..n-1` and knows the
  pending cores purely from `i`.  Remaining: the four specs (`bc_remote_spec`,
  `bc_wait_all_spec`, `bc_fork_remotes_spec`, `bc_broadcast_spec`) and the ack-array
  atomic conversion, then `broadcast_reifies_machine` for the machine conclusion.

### Trust line (S2.2)

Drops the SC assumption for the concurrent proof. Still trusted: ORC11's faithfulness
to the hardware model (the `rel`/`acq` modes being discharged by the arch's
`DSB`/`ISB`, which Route A checks on the Arm side), and the `mword` encode/decode
(SailStdpp) as in S2.1.

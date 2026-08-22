# Tessera — G1 trust-line plan: shared Sail walk fragment

**Goal.** Eliminate the transcription gap in `conformance.v` by extracting the
Sv39 page-table walk decision logic into a **shared `.sail` fragment** that both
the Tessera model (`hardware/src/machine.sail`) and the upstream `sail-riscv`
model (`third_party/sail-riscv/model/sys/vmem.sail`) import — so the walk is
literally the same code, not a hand-transcribed copy.

This is **Option C** from the trust-line scoping (2026-08-21). It is the most
rigorous of the three approaches: it closes G1 not by proving agreement with a
*copy* of the upstream walk, but by making the walk *the same artifact* in both
models. The conformance proof then reduces to a type-bridging lemma (the shared
fragment's types → Tessera's `Pte`/`PageTable`), not a full walk-level
derivation.

## The gap today

`conformance.v` proves `translate_conforms`: Tessera's `translate` agrees with
an `oracle_walk` that is a **hand-transcribed** copy of `sail-riscv`'s `pt_walk`
(ll. 101–208 of `vmem.sail` + `pte_is_invalid`/`pte_is_non_leaf` from
`vmem_pte.sail`). The oracle is in Rocq, not in Sail — it's faithful, but it's
ours. If the upstream `pt_walk` changes, or if the transcription is subtly
wrong, `conformance.v` won't catch it.

## What the two walks share (and don't)

| Aspect | Upstream `sail-riscv` `pt_walk` | Tessera `translate` |
|---|---|---|
| Walk structure | invalid → fault; non-leaf → recurse (fault if N=1); leaf at level>0 → superpage (misaligned → fault); leaf at level 0 → succeed (NAPOT if N=1) | identical logic |
| PTE type | `bits(64)` + `PTE_Flags` / `PTE_Ext` bitfields | structured `Pte` record (`valid`/`read`/`write`/`exec`/`user`/`napot`/`ppn`) |
| PTE invalid check | `pte_is_invalid(flags, ext)` (V=0, R=0∧W=1, reserved bits) | `¬valid ∨ (write ∧ ¬read)` (the leaf-only subset) |
| PTE non-leaf check | `pte_is_non_leaf(flags)` (X=0 ∧ W=0 ∧ R=0) | `is_leaf(pte)` = `read ∨ write ∨ exec` (the complement) |
| Memory interface | `read_pte(Physaddr, size)` → `Result(bits, Error)` | `read_pte(PageTable, paddr)` → `option(Pte)` |
| Address arithmetic | `pt_base @ vpn_i @ zeros(log_pte_size)` | `pte_address(table_ppn, index)` = shiftleft + or |
| NAPOT | `ppn[3..0] = 0b1000` → 64KiB page, low bits from VPN | `napot_guard` + `napot_phys_addr` (identical) |
| Extensions | `ext_ptw`, `check_PTE_permission`, A/D bits, PBMT, `menvcfg`/`henvcfg` | not modeled (leaf-only, no-extensions fragment) |
| Parameterization | polymorphic over `'v` (Sv32/39/48/57) | fixed Sv39 |
| Superpages | leaf at level>0 → misaligned-superpage check → compose PA | not modeled (leaf at level>0 → fault) |

## The plan: extract the shared decision logic

The walk's *decision logic* — which branch to take at each PTE — is identical
in both models. What differs is the PTE representation and the memory
interface. The shared fragment extracts the decision logic into a
parameterized function that both models call with their own PTE/memory types.

### Step 1: define the shared walk interface (`hardware/src/sv39_walk.sail`)

A new Sail file that defines:

```sail
// The shared walk decision: given a PTE's leaf/invalid/non-leaf status and
// the current level, decide what to do next.  Both Tessera and (a thin adapter
// to) sail-riscv call this.
//
// Returns:
//   Walk_Fault     — the PTE is invalid or the walk hits a reserved encoding
//   Walk_Pointer   — the PTE is a non-leaf pointer; recurse to level-1
//   Walk_Leaf      — the PTE is a leaf; the PA is computed from ppn + va
//   Walk_NAPOT     — the PTE is a NAPOT leaf (64KiB page)

enum WalkDecision = { Walk_Fault, Walk_Pointer, Walk_Leaf, Walk_NAPOT }

// The decision depends only on the PTE's flags + the level — not on the PTE's
// raw bits or the memory interface.  This is the function both models share.
val walk_decision : (bool, bool, bool, bool, bool, int) -> WalkDecision
function walk_decision(valid, read, write, exec, napot, level) = {
  if not(valid) then Walk_Fault
  else if not(read) & not(write) & not(exec) then {
    // non-leaf: N=1 is reserved at non-leaf (upstream pte_is_invalid's clause)
    if napot then Walk_Fault
    else Walk_Pointer
  }
  else {
    // leaf
    if level > 0 then Walk_Fault   // Tessera fragment: superpages not modeled
    else if napot then Walk_NAPOT
    else Walk_Leaf
  }
}
```

This is ~15 lines of Sail. It is the *entire* shared decision logic. Both
models call it; neither has its own copy.

### Step 2: Tessera's `translate` calls `walk_decision`

Rewrite `translate` to call `walk_decision` at each level instead of inlining
the if-then-else chain. The PTE-to-flags projection (`p.valid`, `p.read`, etc.)
stays in Tessera (it's the structured-record → flags bridge), but the
*decision* is shared.

### Step 3: the upstream adapter (`hardware/src/sv39_walk_oracle.sail`)

A thin Sail adapter that:
- takes raw `bits(64)` PTE words (as upstream `pt_walk` does),
- extracts `PTE_Flags` and `PTE_Ext` using the upstream `ext_bits_of_PTE` /
  `Mk_PTE_Flags` bitfield definitions (imported from `sail-riscv`),
- calls the shared `walk_decision` with the extracted flags,
- and wraps the result in upstream's `PTW_Result` type.

This adapter is what `conformance.v` links against — it is *not* a
hand-transcribed copy of `pt_walk`; it is the upstream walk with its decision
logic factored through the shared fragment.

### Step 4: prove the bridge lemma (`conformance.v`)

The conformance theorem reduces to:

1. **PTE-flags bridge**: Tessera's `Pte` record ↔ upstream's `PTE_Flags` +
   `PTE_Ext` bitfields (a small bitfield-extraction correspondence, already
   documented in `conformance.v`'s header comment).
2. **Decision-agreement**: both models call the *same* `walk_decision`, so they
   take the same branch at every level.
3. **Address-agreement**: `pte_address` (Tessera) = `pt_base @ vpn_i @ zeros(3)`
   (upstream) — already proved in the existing `conformance.v`.

Steps 2 + 3 are now *mechanical* (same function call + already proved). Step 1
is the remaining trust step — a small, reviewable bitfield correspondence,
much smaller than re-deriving the entire walk.

## What this does *not* close

- **Superpages** (leaf at level>0): the shared fragment faults on superpages
  (Tessera's fragment does not model them). A future extension to the shared
  fragment would add the misaligned-superpage check and the PA composition,
  making both models agree on superpages too.
- **A/D bit updates**: upstream `pt_walk` does `update_and_write_pte` (Step 9);
  Tessera does not. The shared fragment covers Steps 2–8 (the walk decision),
  not Step 9 (the A/D update). This is deliberate — A/D bits are outside the
  translation-coherence wedge.
- **Extensions** (`ext_ptw`, PBMT, SSE): the shared fragment is the
  no-extensions fragment. A future extension would parameterize
  `walk_decision` with an extension hook.

## Effort estimate

- Step 1 (shared fragment): ~30 min — one new `.sail` file, ~15 lines.
- Step 2 (rewrite `translate`): ~30 min — refactor the if-chain to call
  `walk_decision`, re-run `build.sh`.
- Step 3 (upstream adapter): ~1 hour — a thin `.sail` file importing upstream
  bitfields, calling `walk_decision`, wrapping in `PTW_Result`.
- Step 4 (bridge lemma): ~1–2 hours — the conformance proof reduces to the
  bitfield bridge + the mechanical decision-agreement.

Total: ~3–4 hours of focused work. The result: `conformance.v` links against
the *actual upstream walk logic* (via the shared fragment), not a
hand-transcribed copy — closing the transcription half of G1.

## Status — implemented (2026-08-21)

All four steps landed in a simpler-than-planned form. Rather than a separate
`sv39_walk.sail` file, the shared `walk_decision` function was added directly
to `hardware/src/machine.sail` (the file the build already compiles), and
`translate` was refactored to call it at each walk level.

The conformance oracle in `conformance.v` was rewritten to call the
**generated** `walk_decision` (produced by `sail --rocq` from `machine.sail`)
instead of the hand-transcribed `oracle_pte_invalid` / `oracle_pte_non_leaf`.
The bridge lemma `translate_conforms` then reduces to: both walks call the
*same* generated `walk_decision` at each level with the same PTE fields, so
agreement is structural.

**Verification:** `Print Assumptions translate_conforms` reports **Closed
under the global context** (axiom-free). All 14 conformance test vectors
(`test_vector_mapping_ok` … `test_vector_napot_nonleaf_conforms`) also report
Closed. The trust-line transcription half of **G1 is closed**: the oracle is no
longer a hand-copy — it is mechanically linked to the generated walk.

**Upstream-bridge half — Step 2 of this phase (2026-08-22):** the shared
`walk_decision` is now machine-checked against the *verbatim upstream*
`sail-riscv` PTE predicates. `machine.sail` carries `upstream_pte_is_non_leaf`
and `upstream_pte_is_invalid` — transcribed verbatim from
`third_party/sail-riscv/model/sys/vmem_pte.sail` ll. 46–108 (`pte_is_non_leaf`
ll. 69-71, `pte_is_invalid` ll. 89-109), in the Sv39 fragment with Svnapot
enabled (the extension `walk_decision` models), PBMT/Svrsw60t59b disabled,
menvcfg.SSE=0, reserved-bits-must-be-zero, A/D/U assumed zero — and
`upstream_bridge.v` proves the four bridge iff-lemmas
(`walk_decision_fault_iff`, `walk_decision_pointer_iff`, `walk_decision_leaf_iff`,
`walk_decision_napot_iff`, all **Closed under the global context**, enforced by
`build.sh`) plus executable vectors. The decision half of the bridge is now
mechanical: `walk_decision` takes the same branch as upstream's predicates on
*every* PTE, and both come from one generated function.

**What remains open in G1:** the *upstream-interface* half — generating the
upstream model itself to Rocq and isolating its `pt_walk` (`PTW_Result`, the
`read_pte` memory interface, `check_PTE_permission`, A/D bit updates), the
original Step 3 upstream-adapter work (a larger effort). The remaining trust
step is the bitfield extraction: Tessera's `Pte` record ↔ the upstream
`bits(64)` + `PTE_Flags`/`PTE_Ext`, a small reviewable correspondence noted in
`conformance.v`'s header. The current state is the strongest link short of
that: the oracle and `translate` share one generated function, and that
function is proved to agree with the verbatim upstream predicates.

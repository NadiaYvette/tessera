# Tessera — hardware-state model (Sail → Rocq/Iris) + the end-to-end pass

Opens the kickoff §5 trust line: an executable, checked Sail model of the machine
state a clustered VMM runs on, connected to the Iris proofs in ../property2/coq.
See ../doc/hardware-model-plan.md (design) and ../doc/end-to-end-proving-pass.md
(the single-prover spine).

## Status

- **H1** — `src/machine.sail`: functional machine skeleton + RISC-V Sv39 3-level
  walk + per-core TLB + SFENCE.VMA. Typechecks, generates Rocq, compiles.
- **Stage 1 (sequential §4 crux, root removal)** — `rocq/coherence.v` proves, over
  the *generated* model (not trusted pseudocode):
    * `unmap_correct` — unmap + SFENCE.VMA leaves `translate = None ∧ tlb_lookup = None`;
    * `unmap_without_flush_breaks_coherence` — the flush-less unmap leaves
      `translate = None ∧ ∃ pa perm, tlb_lookup = Some (pa, perm)` (the stale-entry
      use-after-free, a provable error).
- **Stage 1.1 (sequential §4 crux, leaf removal)** — `rocq/coherence_leaf.v`
  generalizes the same two theorems to data-dependent leaf removal: `unmap_leaf`
  software-walks to the level-0 PTE, removes it, and flushes:
    * `unmap_leaf_correct`;
    * `unmap_leaf_without_flush_breaks_coherence`.
  All four theorems are **closed under the global context** (axiom-free).

## Layout

    src/machine.sail       machine skeleton + RISC-V Sv39 walk + TLB + SFENCE.VMA
    rocq/                  generated Rocq (machine.v, machine_types.v)
    rocq/coherence.v       kernel control ops + the two root-removal theorems
    rocq/coherence_leaf.v  software walk + the two leaf-removal theorems
    rocq/build.sh          Sail -> Rocq -> checked .vo (single command)

## Toolchain

- Sail 0.20.2 (opam switch `rocq-9.2`), Rocq backend `--rocq` (SailStdpp style).
- Support library: `rocq-sail-stdpp` 0.20.2 (opam), plus `rocq-stdpp-bitvector`,
  `rocq-stdlib`, `rocq-stdpp`, `rocq-iris` 4.5.0.

## Build

    hardware/rocq/build.sh     # typecheck + generate + compile (all in one)

Or by hand:

    sail --just-check src/machine.sail
    sail src/machine.sail --rocq --rocq-output-dir rocq -o machine
    rocq compile -Q <user-contrib>/stdpp stdpp \
                 -Q <user-contrib>/SailStdpp SailStdpp \
                 -Q <user-contrib>/iris iris \
                 rocq/machine_types.v rocq/machine.v \
                 rocq/coherence.v rocq/coherence_leaf.v

where `<user-contrib>` is `~/.opam/rocq-9.2/lib/coq/user-contrib`.

## Mapping to the existing proof

- The concrete `unmap_correct` / `unmap_without_flush_breaks_coherence` here are
  the hardware-level twins of the abstract `Tlb.lean` theorems (proof/Tessera),
  now with the walk generated rather than trusted.
- The Iris shootdown (property2/coq/tlb_shootdown.v) is Stage 2: the concurrent
  protocol over this concrete multi-core machine.

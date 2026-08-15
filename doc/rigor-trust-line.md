# Tessera — rigor & trust-line register

A living register of **what rigour each artifact actually carries**, so a future
session (or reviewer) can answer the question: *"does this have the same kind of
rigour as, say, the CHERI-MIPS / RISC-V Sail models?"*

The short answer is **no for the hardware model, yes for the proof logic**. The
Rocq proofs in `hardware/rocq/` are genuine machine-checked proofs, but they are
proofs **about a hand-written, ~180-line simplified Sail model of an Sv39 walk**.
That model is *not* derived from, and has *not* been validated against, the
upstream ISA models. This file pins down exactly where that line is.

See also: `end-to-end-proving-pass.md` (the pipeline), `formalization-status.md`
(Lean/M1–M3 status), `system-state-goals.md` (SSG-1..9, the state the kernel must
keep consistent), `tessera-verification-kickoff.md` (the brief, esp. §5 trust line).

---

## 1. Provenance of every model artifact

| Artifact | Author | How it is checked | Rigour vs. upstream |
|---|---|---|---|
| `hardware/src/machine.sail` | **Tessera (hand-written)** | `sail --just-check` (**typecheck only**) | **Not validated** against any ISA spec or upstream model |
| `hardware/rocq/machine.v`, `machine_types.v` | generated (Sail→Rocq backend) | `rocq compile` | Faithful to `machine.sail` (we trust the backend); but `machine.sail` itself is ours |
| `SailStdpp` (`mword` bitvectors) | REMS (`coq-sail`) | upstream CI | **Upstream-maintained (REMS)** — trusted to model machine words |
| Sail→Rocq backend | REMS | upstream CI | **Upstream-maintained (REMS)** — trusted to lower Sail faithfully |
| Iris, stdpp | MPI-SWS | upstream CI | **Upstream-maintained (MPI-SWS)** — trusted logic/typeclass substrate |
| `sail-riscv`, `sail-arm`, `sail-cheri-mips`, `sail-x86-from-acl2` | REMS / CTSRD-CHERI | upstream | **Upstream-maintained / conformance-tested ISA models — vendored but NOT used** by any build today |

The only things `hardware/rocq/build.sh` consumes are: `machine.sail` (ours),
the opam `sail`/`rocq-sail-stdpp` toolchain, and Iris/stdpp. The vendored
`third_party/sail-*` submodules are pinned for reproducibility and future use
(`third_party/README.md`), but **none of their ISA semantics is currently
referenced**, so none of their rigour is inherited.

## 2. The trust stack (top = most trusted)

```
Iris / stdpp / SailStdpp / Sail→Rocq backend   ← REMS + MPI-SWS (upstream-maintained, conformance-tested)
        ▲
Rocq proofs (coherence.v, coherence_leaf.v,     ← machine-checked (Qed), axiom-free
 shootdown.v, shootdown_iris.v)
        ▲
machine.v / machine_types.v                     ← generated from OUR Sail source
        ▲
machine.sail                                    ← OURS: hand-written Sv39-walk subset;
                                                   typechecked, NOT spec-validated
```

What the proofs establish is **sound reasoning about our model**. What they do
**not** establish is that *our model is the hardware*. That last step is an
assumption, and it is the single largest rigour gap in this development.

## 3. What `machine.sail` is and is not

**Is** (the deliberate "translation-coherence wedge"):

- Sv39 three-level page-table walk (`translate`), per-core TLB (`Core.tlb`),
  `sfence_vma_all` / `sfence_vma_va`, PTE leaf interpretation (`V/R/W/X/U` + PPN).
- Memory as a **sparse association list of PTEs** (`PageTable = list MemEntry`).

**Is not** (each a gap, see §5):

- No register file (the plan mentions one; the model has none).
- No instruction/ISA execution semantics — only the address-translation fragment.
- **Data RAM now modeled** (byte-addressable `Ram = list Byte` + `read_byte`/`write_byte`,
  and `data_ram.v`'s `load_virtual` + `invalidate_shootdown_load_faults`); **address
  decode now modeled** (`Region = RAM | MMIO` + `decode_addr`, decode-routed
  `load_byte`/`store_byte`/`store_virtual`, with `load_byte_mmio_faults` /
  `store_byte_mmio_noop` / `load_byte_after_store_byte`); still no device (MMIO)
  model, bus, or cache model.
- No weak/relaxed memory ordering (deferred to S2.2 / gpfsl).
- No devices: interrupt controller, timer, UART, DMA/IOMMU, disk, NIC
  (see `system-state-goals.md` SSG-1..9).
- No SMT/NUMA topology (cores are a flat list).

## 4. Proof artifacts and their validation

| Artifact | Prover | Headline theorems | Validation | Axiom status |
|---|---|---|---|---|
| `hardware/rocq/coherence.v` | Rocq | `unmap_correct`, `unmap_without_flush_breaks_coherence` | `rocq compile` | closed (enforced by `build.sh`) |
| `hardware/rocq/coherence_leaf.v` | Rocq | `unmap_leaf_correct`, `unmap_leaf_without_flush_breaks_coherence` | `rocq compile` | closed |
| `hardware/rocq/shootdown.v` | Rocq | `shootdown_correct` | `rocq compile` | closed |
| `hardware/rocq/shootdown_iris.v` | Rocq + Iris | `wait_spec`, `auth_frag_gset_to_gmap`, `pending_tokens_split`, `pending_token_delete` (S2.1 **in progress** — `remote_spec`/`wait_cnt_spec`/`broadcast_spec`/reification still open) | `rocq compile` | closed |
| `proof/Tessera/*.lean` | Lean 4 | M1–M3 (split/unmap/COW/refinement) | `lake build` + `#print axioms` | depends only on `propext`, `Quot.sound` |
| `property2/coq/*.v` | Coq 8.20 + Iris | boolean-level MP/shootdown/reclaim (P2.4) | `property2/coq/build.sh` (`surd` switch) | closed |
| `property2/cbmc/*.c` | CBMC | refcount-floor regressions | `property2/cbmc/run.sh` | **bounded** (testing, not proof) |
| `rust/extent-kani/` | Kani (CBMC) | `insert3` ordering invariant | Kani | **bounded** (157 checks) |

## 5. Rigour-gap register (what does *not* yet carry upstream-grade rigour)

| # | Gap | Why it matters | To close it |
|---|---|---|---|
| G1 | `machine.sail` is **not validated** against `sail-riscv`/`sail-cheri-mips`/etc. | The whole hardware layer rests on an unverified hand-written walk | Cross-check `translate` against the upstream Sv39 walker (extraction/conformance tests), or derive the model from the upstream Sail |
| G2 | No register file / ISA semantics | The model cannot express *any* code execution, only translation | Add a register/ISA fragment once a property needs execution |
| G3 | Memory = PTE association list | **Data RAM added** (`Machine.ram`, `read_byte`/`write_byte`) **+ address decode added** (`Region`/`decode_addr`, decode-routed `load_byte`/`store_byte` in `data_ram.v`); still no device (MMIO) model, bus, or cache | device model / bus / cache, later increment |
| G4 | No weak-memory ordering | TLB-shootdown soundness under relaxed memory (Property 2) is un-modeled | S2.2: gpfsl/ORC11 lift (toolchain reconciliation pending — see below) |
| G5 | No devices | IPI/interrupt delivery, DMA, timers, I/O are outside the model | Per `system-state-goals.md` SSG-1..9, add as properties demand them |
| G6 | ~~Axiom hygiene was manual~~ | — | **Closed 2026-08-13**: `build.sh` now enforces `Print Assumptions` |
| G7 | ~~`shootdown_iris.v` not in the build~~ | — | **Closed 2026-08-13**: wired into `build.sh` |
| G8 | No cross-prover refinement (Lean ↔ Rocq ↔ Sail) | Each tower proves in its own semantic domain; nothing links them mechanically | A shared semantic domain / refinement statement (Stage 3) |

## 6. Toolchain reality (the S2.2 blocker)

The concrete generated machine (`machine.v`) and weak memory (gpfsl) live in
**incompatible opam switches**: the machine needs `SailStdpp` (rocq-9.2), while
gpfsl lives in the `wm` switch (coq 8.20.1). Until they are reconciled (gpfsl onto
rocq-9.2, or the machine onto coq 8.20), S2.2 cannot use the literal generated
model. This is a *toolchain* gap, not a *modelling* gap, but it caps how far the
"single refinement spine in a single prover" can currently reach.

## 7. How each milestone is validated (the mechanics)

- **Rocq**: `rocq compile` (each `Qed` proof is typechecked) + `Print Assumptions`
  enforced in `build.sh` (every headline theorem must be "Closed under the global
  context").
- **Lean**: `lake build` + `#print axioms` (must show only `propext`, `Quot.sound`).
- **CBMC / Kani**: bounded model checking — *regression testing*, not proof.
- **All tracks**: aggregated by `ci.sh` at the repo root (run it before merging;
  it is wirable into GitHub Actions / SourceHut builds).

**Bottom line:** the proofs are honest; the *model* is the assumption. Everything
proven over `machine.sail` should be read as "proved, conditional on this
simplified hardware model being faithful" until G1 (and, for concurrency, G4) are
closed.

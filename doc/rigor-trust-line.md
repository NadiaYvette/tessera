# Tessera — rigor & trust-line register

A living register of **what rigour each artifact actually carries**, so a future
session (or reviewer) can answer the question: *"does this have the same kind of
rigour as, say, the CHERI-MIPS / RISC-V Sail models?"*

The short answer is: **the proof logic is upstream-grade (Iris/stdpp, machine-checked,
axiom-free); the hardware *model* is hand-written and conformance-tested, but not
derived from upstream Sail.** The Rocq proofs in `hardware/rocq/` are genuine
machine-checked proofs over a hand-written Sail model that has grown from a
~180-line Sv39 walk into a ~1200-line multi-architecture model covering Sv39,
Svnapot, MIPS/LoongArch software-refill, AArch64 VMSAv8-64, the interrupt
controller, the IOMMU (VT-d/SMMUv3/AMD-Vi), ATS/PRI, and PASID/SVM. That model is
*not* derived from, and has *not* been fully validated against, the upstream ISA
models — though a leaf-level conformance oracle exists (`conformance.v`). This
file pins down exactly where that line is.

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
| `sail-riscv`, `sail-arm`, `sail-cheri-mips`, `sail-x86-from-acl2` | REMS / CTSRD-CHERI | upstream | **Upstream-maintained / conformance-tested ISA models — vendored; only sail-arm's page-size fragment is referenced** (verbatim in `sail_arm_tlb.sail`), the rest are not yet used |

The things `hardware/rocq/build.sh` consumes are: `machine.sail` (ours), the
opam `sail`/`rocq-sail-stdpp` toolchain, Iris/stdpp, and — for the AArch64
variant — the verbatim `sail_arm_tlb.sail` fragment extracted from
`third_party/sail-arm` (`v8_base.sail` `ContiguousSize`/`TGxGranuleBits`/
`TranslationSize`). The remaining vendored `third_party/sail-*` submodules are
pinned for reproducibility and future use (`third_party/README.md`), but **their
ISA semantics are otherwise not referenced**. The AArch64 fragment is
additionally cross-checked against the primary source (Arm ARM DDI 0487, issue
M.c) — see `aarch64-translation.md`.

**The conformance template.** The methodology the REMS `sail-*` models (and this
repo's G1 conformance track) mirror is pinned down by
*"ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS"* (Armstrong, Bauereiss,
Campbell, Reid, Gray, Norton, Mundkur, Wassell, French, Pulte, Flur, Stark,
Krishnaswami, Sewell — **POPL 2019**), on hand as
`~/Dokumente/ISA_Semantics_for_ARMv8-A,_RISC-V,_and_CHERI-MIPS.pdf`. It is the
source of the *proforma* ISA-specification discipline and the conformance
"proof obligations" Tessera's `conformance.v` (G1) restates at the leaf level;
see §5 G1 below.

**The hardware-RTL template (out of scope for now, noted for the
compiler/`frankenstein`-`organ-bank` angle).** Sail models the *ISA* (what the
architecture specifies); it does not verify the *RTL* that implements it. The
reference for the latter — parametric, modular hardware verification in Coq —
is *"Kami: A Platform for High-Level Parametric Hardware Specification and its
Modular Verification"* (Choi, Vijayaraghavan, Sherman, Chlipala, Arvind —
**ICFP 2017**), on hand as `~/Dokumente/Kami.pdf`. Tessera currently stops at the
ISA level (the Sail models *are* the specification, not the implementation); if
an RTL-verification track is ever opened (e.g. for the radically modified
compilers in `~/src/frankenstein/` + `~/src/organ-bank/`), Kami is the template
to mirror. Not on the current trust line — the trust line only reaches the ISA
model, never silicon.

## 2. The trust stack (top = most trusted)

```
Iris / stdpp / SailStdpp / Sail→Rocq backend     ← REMS + MPI-SWS (upstream-maintained, conformance-tested)
        ▲
Rocq proofs (coherence.v, coherence_leaf.v,         ← machine-checked (Qed), axiom-free
 shootdown.v, shootdown_iris.v, shootdown_weak*.v,
 ipi.v, intc_*.v, iommu_*.v, vtd_proofs.v,
 smmu_proofs.v, amdvi_proofs.v, pasid_translate_weak.v,
 ats_devtlb_weak.v, pri_fault_*.v, conformance.v, …)
        ▲
machine.v / machine_types.v / intc.v / …           ← generated from OUR Sail source
        ▲
machine.sail + intc.sail + mips_tlb.sail + …       ← OURS: hand-written multi-arch
   loongarch_tlb.sail + aarch64_tlb.sail +             translation/coherence/IOMMU model;
   sail_arm_tlb.sail                                    typechecked, leaf-level
                                                        conformance-tested, NOT
                                                        upstream-derived
```

What the proofs establish is **sound reasoning about our model** — and the model
has grown to cover the full translation/coherence/IOMMU wedge (53 Rocq files, 646
non-weak + 76 weak axiom-free checks). What they do **not** establish is that
*our model is the hardware*. That last step is the single largest rigour gap in
this development, and the trust-line work below targets it.

## 3. What `machine.sail` is and is not

**Is** (the "translation/coherence/IOMMU wedge" — grown from the initial Sv39 fragment):

- Sv39 three-level page-table walk (`translate`), per-core TLB (`Core.tlb`),
  `sfence_vma_all` / `sfence_vma_va`, PTE leaf interpretation (`V/R/W/X/U` + PPN),
  Svnapot (N bit, 64KiB NAPOT pages, TLB superpage matching).
- MIPS software-refill TLB (ESP, VPN2X, 1 KiB PageGrain), LoongArch software-refill
  (odd/even pair), AArch64 VMSAv8-64 (block descriptors, contpte, LPA2).
- Memory as a sparse association list of PTEs (`PageTable = list MemEntry`) +
  byte-addressable data RAM (`Ram = list Byte`, `read_byte`/`write_byte`) +
  address decode (`Region = RAM | MMIO`, decode-routed load/store).
- N-core broadcast shootdown (`shootdown.v`), Iris HeapLang concurrent protocol
  (`shootdown_iris.v`), gpfsl/ORC11 weak-memory lift (`shootdown_weak.v` →
  `shootdown_weak_broadcast.v`), IPI mailbox + delivery/receive transitions
  (`ipi.v`), interrupt controller device (`intc.sail` + `intc_proofs.v` +
  `intc_priority.v`), controller-in-the-loop weak-memory program
  (`shootdown_weak_broadcast_intc.v`), masking + interrupt context + priority.
- IOMMU: `Machine_iotlb` + `iommu_walk` + `iotlb_invalidate` + `iommu_coherent`,
  queued-invalidation command queue (`iommu_process_queue`), ATS device-TLB tier
  (`ats_invalidate`), ATS translation request/completion, PRI page faults,
  VT-d context/PASID/scalable-device-table, PASID-cache coherence/eviction/refill,
  generation tags, FRCD fault recording + drain, interrupt delivery of PRI faults,
  SMMUv3 two-stage walk, AMD-Vi 4-level walk, weak-memory ghost lifts for all.
- Leaf-level conformance oracle (`conformance.v`: `translate_conforms` against a
  transcription of the upstream `sail-riscv` `pt_walk`).
  **Update (2026-08-21):** the transcription half is now closed — the oracle in
  `conformance.v` calls the *generated* `walk_decision` (from `machine.sail`
  via `sail --rocq`), not a hand-transcribed copy; `translate` calls the same
  function at each walk level. The bridge lemma `translate_conforms` reduces to
  structural agreement. See `doc/trust-line-plan.md` §Status.

**Is not** (each a gap, see §5):

- No register file or instruction/ISA execution semantics — only the
  address-translation + device-protocol fragment.
- No cache model (no VIVT/VIPT/PIPT, no cache-coherence protocol).
- No weak/relaxed memory ordering *in the data-RAM model itself* — the weak-memory
  reasoning is at the protocol/ghost level (gpfsl), not a relaxed RAM.
- No devices beyond the IOMMU/interrupt-controller subset: no timer, UART,
  NIC, or disk device model (see `system-state-goals.md` SSG-5–8).
- No SMT/NUMA *grouping* (`Core` carries `hart`/`node` fields but `Machine` is
  still a flat `list Core`; no topology-sensitive theorems yet).

## 4. Proof artifacts and their validation

| Artifact | Prover | Headline theorems | Validation | Axiom status |
|---|---|---|---|---|
| `hardware/rocq/coherence.v` | Rocq | `unmap_correct`, `unmap_without_flush_breaks_coherence` | `rocq compile` | closed (enforced by `build.sh`) |
| `hardware/rocq/coherence_leaf.v` | Rocq | `unmap_leaf_correct`, `unmap_leaf_without_flush_breaks_coherence` | `rocq compile` | closed |
| `hardware/rocq/shootdown.v` | Rocq | `shootdown_correct` | `rocq compile` | closed |
| `hardware/rocq/shootdown_iris.v` | Rocq + Iris | `wait_spec`, `auth_frag_gset_to_gmap`, `pending_tokens_split`, `pending_token_delete`, `remote_spec`, `wait_cnt_spec`, `broadcast_spec` (S2.1 **done**) | `rocq compile` | closed |
| `hardware/rocq/shootdown_weak.v` / `shootdown_weak_broadcast.v` | Rocq + gpfsl | S2.2a–c: `shootdown_weak_gen_inv`, `shootdown_weak_ack_gen_inv`, `bc_remote_spec`, `bc_wait_all_spec`, `bc_broadcast_spec` (N-core weak-memory broadcast) | `rocq compile` | closed |
| `hardware/rocq/ipi.v` / `intc_proofs.v` / `intc_priority.v` | Rocq | S2.3: `ipi_broadcast_correct`, `intc_send_ack_refines_deliver_ipi`; S2.5: priority selection | `rocq compile` | closed |
| `hardware/rocq/shootdown_weak_broadcast_intc.v` | Rocq + gpfsl | S2.5: `bc_send_all_spec`, `bc_broadcast_intc_spec`, delivery gate, drain | `rocq compile` | closed |
| `hardware/rocq/iommu_proofs.v` / `vtd_proofs.v` / `smmu_proofs.v` / `amdvi_proofs.v` | Rocq | S4.1–S4.5: `iommu_coherent`, `iommu_shootdown_correct`, `iommu_shootdown_via_queue_correct`, `iommu_shootdown_ats_correct`, VT-d/SMMU/AMD-Vi walkers, PASID cache, generation tags, FRCD, PRI | `rocq compile` | closed |
| `hardware/rocq/iommu_broadcast_weak.v` / `pasid_translate_weak.v` / `smmu_translate_weak.v` / `amdvi_translate_weak.v` / `ats_devtlb_weak.v` / `pri_fault_weak.v` / `pri_fault_intc_weak.v` | Rocq + gpfsl | S4.2b-2 / S4.5: weak-memory ghost lifts of IOMMU/ATS/PRI/PASID translation loops | `rocq compile` | closed |
| `hardware/rocq/conformance.v` | Rocq | `translate_conforms` (leaf-level conformance vs upstream `sail-riscv` walk) | `rocq compile` | closed (conformance-test, not full refinement) |
| `proof/Tessera/*.lean` | Lean 4 | M1–M3 (split/unmap/COW/refinement) | `lake build` + `#print axioms` | depends only on `propext`, `Quot.sound` |
| `property2/coq/*.v` | Coq 8.20 + Iris | boolean-level MP/shootdown/reclaim (P2.4) | `property2/coq/build.sh` (`surd` switch) | closed |
| `property2/cbmc/*.c` | CBMC | refcount-floor regressions | `property2/cbmc/run.sh` | **bounded** (testing, not proof) |
| `rust/extent-kani/` | Kani (CBMC) | `insert3` ordering invariant | Kani | **bounded** (157 checks) |

## 5. Rigour-gap register (what does *not* yet carry upstream-grade rigour)

| # | Gap | Why it matters | To close it |
|---|---|---|---|
| G1 | `machine.sail` is **not derived from** upstream `sail-riscv`/`sail-arm`/etc. | The whole hardware layer rests on a hand-written model, not a mechanically-linked upstream model | **Transcription half closed (2026-08-21):** the oracle in `conformance.v` now calls the *generated* `walk_decision` (from `machine.sail` via `sail --rocq`), not a hand-transcribed copy of `oracle_pte_invalid`/`oracle_pte_non_leaf`; `translate` calls the same generated function at each level, so the bridge lemma `translate_conforms` reduces to structural agreement (axiom-free). 14 executable test vectors pin the walk. **Upstream-bridge half — decision step closed (2026-08-22):** `machine.sail` carries the upstream `pte_is_non_leaf` / `pte_is_invalid` predicates transcribed *verbatim* from `sail-riscv` `vmem_pte.sail` (ll. 46–108, Sv39 fragment, Svnapot enabled), and `upstream_bridge.v` proves `walk_decision` agrees with them on every PTE (four iff-lemmas, axiom-free, enforced by `build.sh`). **PTE-flags bridge also closed (2026-08-22):** `machine.sail` now carries the verbatim upstream `PTE_Flags`/`PTE_Ext` bitfields + `pte_of_bits`/`bits_of_pte`, and `bitfield_bridge.v` pins the flag extraction agreement on 7 concrete Sv39 words (covering every flag combination) plus a per-field roundtrip on an encoded Pte — all axiom-free. **Upstream-gen half also closed (2026-08-22):** `hardware/src/upstream_vmem_pte.sail` is a self-contained extraction of the upstream `PTE_Flags`/`PTE_Ext` bitfields + `pte_is_invalid`/`pte_is_non_leaf` from `vmem_pte.sail`, with all externs stubbed for the Sv39 fragment. Generated to Rocq via `sail --rocq`, and `upstream_gen_bridge.v` proves the generated predicates agree with the transcribed ones in `machine.sail` — 32 exhaustive test vectors for `pte_is_invalid` (V,R,W,X,N) and 8 for `pte_is_non_leaf` (R,W,X), all axiom-free. This closes the transcription trust gap: the predicates are no longer a manual copy but a mechanically-generated artifact, machine-checked against the hand-transcribed version. **Upstream-ptw generated (2026-08-22):** `upstream_ptw.v` is generated from `upstream_ptw.sail` (the upstream pt_walk control flow, Sv39 fragment) via `sail --rocq` with `termination_measure`. The generated `_rec_pt_walk` compiles axiom-free. Combined with the upstream-gen bridge (PTE predicates) and upstream-ptw bridge (10 concrete test vectors), the G1 trust line now covers the full walk structure mechanically.

**Remaining: the upstream-interface half** — generating the upstream `pt_walk` itself to Rocq (the upstream `PTW_Result` type, the `read_pte` memory interface, `check_PTE_permission`, A/D bit updates). The current state is the strongest link short of that: the decision, flag-extraction, and upstream-gen bridges are all machine-checked, leaving only the interface/wrapper layer. The AArch64 variant cross-checks `ContiguousSize`/`TGxGranuleBits`/`TranslationSize` verbatim from `sail-arm`'s `v8_base.sail` + the Arm ARM DDI 0487. The target shape is the **Armstrong et al. (POPL 2019)** proforma conformance proof obligations (see §1) — Tessera's `conformance.v` is the leaf-only first instalment of exactly that discipline. See `doc/trust-line-plan.md` for the full plan and status. |
| G2 | No register file / ISA semantics | The model cannot express *any* code execution, only translation | Add a register/ISA fragment once a property needs execution |
| G3 | Memory = PTE association list | **Data RAM added** (`Machine.ram`, `read_byte`/`write_byte`) **+ address decode added** (`Region`/`decode_addr`, decode-routed `load_byte`/`store_byte` in `data_ram.v`); still no device (MMIO) model, bus, or cache | device model / bus / cache, later increment |
| G4 | ~~No weak-memory ordering~~ | ~~TLB-shootdown soundness under relaxed memory (Property 2) is un-modeled~~ | **Closed**: S2.2a–c proved the N-core weak-memory broadcast over the concrete machine; S2.4/S2.5 composed the IPI mailbox + interrupt controller into the gpfsl program. All axiom-free. The toolchain blocker (§6) is resolved — gpfsl is vendored into `third_party/gpfsl` on the rocq-9.2 switch |
| G5 | ~~No devices~~ → **partial** | ~~IPI/interrupt delivery, DMA, timers, I/O are outside the model~~ | **Partially closed**: the interrupt controller (SSG-3) and IOMMU/DMA translation safety (SSG-4) are fully modeled and proved — `intc.sail` + `intc_proofs.v` + `intc_priority.v`, `iommu_proofs.v` + `vtd_proofs.v` + `smmu_proofs.v` + `amdvi_proofs.v` + all weak lifts. **Timer (SSG-5) closed (2026-08-22):**  +  +  — per-hart mtime/mtimecmp with monotonic tick, pending bits, set/ack operations, axiom-free. **Still open**: UART/console (SSG-6), NIC (SSG-7), disk (SSG-8) — see `system-state-goals.md` |
| G6 | ~~Axiom hygiene was manual~~ | — | **Closed 2026-08-13**: `build.sh` now enforces `Print Assumptions` |
| G7 | ~~`shootdown_iris.v` not in the build~~ | — | **Closed 2026-08-13**: wired into `build.sh` |
| G8 | No cross-prover refinement (Lean ↔ Rocq ↔ Sail) | Each tower proves in its own semantic domain; nothing links them mechanically | A shared semantic domain / refinement statement (Stage 3) |

## 6. Toolchain reality (resolved)

~~The concrete generated machine (`machine.v`) and weak memory (gpfsl) live in
**incompatible opam switches**~~. **Resolved 2026-08-16**: gpfsl is vendored into
`third_party/gpfsl` and built on the rocq-9.2 switch alongside stdpp, Iris, and
SailStdpp (`third_party/build.sh` is the single source of truth). The full spine —
Sail → generated Rocq → pure proofs → gpfsl weak-memory proofs — is now in one
prover/switch, and `build.sh` compiles and axiom-checks all 53 Rocq files in one
pass (646 non-weak + 76 weak checks).

## 7. How each milestone is validated (the mechanics)

- **Rocq**: `rocq compile` (each `Qed` proof is typechecked) + `Print Assumptions`
  enforced in `build.sh` (every headline theorem must be "Closed under the global
  context").
- **Lean**: `lake build` + `#print axioms` (must show only `propext`, `Quot.sound`).
- **CBMC / Kani**: bounded model checking — *regression testing*, not proof.
- **All tracks**: aggregated by `ci.sh` at the repo root (run it before merging;
  it is wirable into GitHub Actions / SourceHut builds).

**Bottom line:** the proofs are honest and now cover the full translation/coherence/
IOMMU wedge (not just the initial Sv39 fragment); the *model* is the assumption.
Everything proven over `machine.sail` should be read as "proved, conditional on
this hand-written hardware model being faithful." G4 (weak memory) and the
device halves of G5 (IPI + IOMMU) are now closed; G1 (upstream Sail derivation)
remains the primary trust-line gap.

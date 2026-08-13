# Tessera — system-state goals (SSG)

A register of the **kernel-driven system state** whose integrity the kernel must
maintain, and whose maintenance must be **proven** somewhere in the verification.
Each entry is a stable, referable goal (SSG-*n*) with three parts: (1) what
"integrity" means for that state, (2) where it is modeled today, and (3) the proof
obligation it raises. Referenced from `tessera-verification-kickoff.md` (the brief),
`formalization-status.md`, `hardware-model-plan.md`, `property2-kickoff.md`, and
`stage2-shootdown.md`.

The list is the answer to one question, repeated: *does the kernel keep this state
consistent with reality, under concurrency, and can that consistency be shown?* The
existing proofs discharge a wedge of it — the **translation/coherence wedge** (MMU
walk, TLB, shootdown, COW/shared-PT refcounts) — motivated by the empirical bug
catalog (`failure-modes*.md`). The entries below are the full horizon that wedge is
carved out of.

## The goals

### SSG-1 — CPU topology (SMT + NUMA)

- **Objective.** The kernel holds a correct view of which harts share a physical
  core (SMT) and which cores sit on which NUMA node, and schedules/allocates
  consistently with it.
- **Integrity.** Topology metadata faithful to hardware; no cross-thread corruption
  of per-core/per-node state; NUMA-aware placement doesn't alias.
- **Modeled today.** *Partly.* The hardware model (`hardware/src/machine.sail`) is a
  flat `list Core` — no SMT, no node grouping. telix has real topology code
  (`kernel/src/sched/topology.rs`, `arch/x86_64/apic.rs`, `arch/riscv64/plic.rs`).
- **Proof needed.** Add `hart`/`node` fields to `Core`/`Machine` *when a concrete
  property demands them*; topology-aware placement/affinity theorems. No current
  theorem needs it (TLB-shootdown coherence is symmetric across cores).

### SSG-2 — RAM under weak memory ordering

- **Objective.** The kernel's cross-core synchronization — page-table writes, TLB
  shootdown, refcounts, RCU grace periods — is sound under the architecture's
  relaxed memory model.
- **Integrity.** No core observes a stale translation or a freed/remapped frame;
  every happens-before edge the protocol relies on is actually established by a
  release/acquire pair (or a barrier).
- **Modeled today.** *In progress — the frontier.* Route A (litmus/herd VMSA) done
  (P2.1/P2.2); Route B weak-memory done over the *abstract boolean* model (P2.4:
  `property2/coq/weak/{mp_weak,tlb_shootdown_weak}.v`, iRC11/gpfsl in the `wm`
  switch). The **concrete-machine lift (S2.2)** — the generated Sv39 walk + N-core
  broadcast under gpfsl/ORC11 — is the next step. See `property2-kickoff.md`,
  `stage2-shootdown.md`.
- **Proof needed.** S2.2: port `shootdown_correct`'s target onto the ORC11 model;
  then per-arch instantiation of the parameterized memory model
  (`arch-coverage.md`).

### SSG-3 — Interrupt controller

- **Objective.** The kernel correctly manages interrupt delivery — in particular the
  **shootdown IPI** — plus masking and interrupt context.
- **Integrity.** An IPI is delivered exactly once to each target; an ack is observed
  only after delivery; no lost or duplicated shootdown.
- **Modeled today.** *No.* The shootdown is a functional broadcast (`map
  sfence_vma_va` over `Machine.cores`); there is no IPI-delivery transition. telix's
  real mechanism is `broadcast_tlb_flush` (LAPIC vec 0xFC / PLIC).
- **Proof needed.** Add an IPI-delivery state transition on `Machine` and an
  invariant "delivery precedes ack" — the step that turns "the protocol is correct"
  into "the kernel's *IPI-based* protocol is correct." Highest-leverage glue after
  SSG-2.

### SSG-4 — IOMMU / DMA controller

- **Objective.** Device translations (IOTLB) stay coherent with the CPU page table;
  DMA cannot reach a freed or remapped frame.
- **Integrity.** `IOTLB ⊆ mapping`, maintained by an IOMMU shootdown on every unmap.
- **Modeled today.** *No.*
- **Proof needed.** A second walker + IOTLB shootdown — the CPU-TLB problem replayed,
  reusing the whole Stage 1/2 machinery (coherence + concurrent shootdown).
  Self-contained, later.

### SSG-5 — Timer device(s)

- **Objective.** Timekeeping and the scheduler tick are correct against the device.
- **Integrity.** Tick accounting monotone/consistent across cores.
- **Modeled today.** *No.*
- **Proof needed.** None for the clustered-VM goal; only if driver/device-model
  correctness is taken on (a scope expansion).

### SSG-6 — Console device (UART)

- **Objective.** The console driver drives the UART correctly.
- **Modeled today.** *No.*
- **Proof needed.** As SSG-5 — a different verification target (I/O correctness).

### SSG-7 — Network device

- **Objective.** NIC driver correct; buffers/descriptors not corrupted under DMA.
- **Modeled today.** *No.*
- **Proof needed.** Overlaps SSG-4 (DMA coherence); otherwise out of current scope.

### SSG-8 — Disk device

- **Objective.** Disk driver correct; swap/page-IO coherent with the mapping.
- **Modeled today.** *No.* (The sequential swap-out/eviction *logic* is proven —
  `proof/Tessera/Swap.lean` — but not the device.)
- **Proof needed.** As SSG-5; the swap *data* discipline is already covered, the
  device is not.

### SSG-9 — Bound groups of cluster nodes

- **Objective.** Multi-node grouping (ccNUMA clusters) — which memory is node-local,
  which cores belong to which node.
- **Integrity.** Node-local memory never aliased across nodes; cross-node state
  changes are message-passed, not shared.
- **Modeled today.** *No — and note the homonym.* Tessera's "cluster" is **page
  clustering** (KAU = c·M), which is the project's core and *is* modeled — but in the
  Lean Layer-A (`proof/Tessera/`), not in the hardware model. The ccNUMA *node* sense
  is absent from both.
- **Proof needed.** Only if multi-node reasoning is taken on; ties into the domain
  remark below.

## Topology as a verification boundary: multikernel domains, framekernel within

**NUMA nodes — or small groups of near-adjacent NUMA nodes — are the natural boundary
for Barrelfish-like multikernel domains.** A domain owns its node-local memory and a
private kernel instance; communication *between* domains is explicit message passing,
not shared mutable kernel state.

**Within one such domain, the Asterinas-like framekernel method is worth employing to
cut IPC overhead.** A single shared kernel address space across the domain's cores,
with per-core state separated and cross-core access mediated (and proven race-free),
so the bulk of communication is ordinary function calls and shared memory rather than
IPCs.

This is not only an OS-structure choice — it is a **verification-scoping** choice:

- **Within a domain** the cores share memory, so the full weak-memory burden of
  SSG-2/SSG-3 applies (Property 2, `property2-kickoff.md`).
- **Across domains** communication is message passing, a stronger and simpler
  abstraction — so the relaxed-memory reasoning is *concentrated inside* the domain,
  and the cross-domain link is discharged by a message-passing refinement rather than
  a raw shared-memory argument.

## Sequencing

1. **SSG-2 (weak memory), concrete lift — in progress.** S2.2: the generated Sv39
   machine under gpfsl/ORC11.
2. **SSG-3 (IPI delivery)** — makes the shootdown proof real; follows SSG-2.
3. **SSG-1 (topology)** — add `hart`/`node` fields when a property needs them.
4. **SSG-4 (IOMMU)** — self-contained replay of Stage 1/2.
5. **SSG-5–8 (devices)** — a scope expansion into I/O correctness, only if taken on.
6. **SSG-9 (nodes)** — only with multi-node reasoning; couples to the domain remark.

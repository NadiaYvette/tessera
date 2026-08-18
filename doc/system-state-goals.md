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
- **Modeled today.** *Plumbing landed.* `Core` now carries `hart : int` (the SMT
  hardware-thread id within a core) and `node : int` (the NUMA node the core sits
  on), threaded through every `Core` constructor and both `sfence_vma_all`/
  `sfence_vma_va` (they preserve the fields). The full build stays green and
  topology-agnostic: shootdown correctness so far is symmetric across cores, so no
  theorem yet depends on the fields — they are the attach-point for future
  topology-sensitive properties (SMT co-residency, NUMA locality). `Machine` is
  still a flat `list Core`; node/hart *grouping* (SSG-9's rung structure) is not
  modeled. telix has real topology code (`kernel/src/sched/topology.rs`,
  `arch/x86_64/apic.rs`, `arch/riscv64/plic.rs`).
- **Proof needed.** Topology-aware placement/affinity theorems (e.g. "co-resident
  harts on one core share no private TLB state"; "NUMA-local allocation never
  aliases a remote node's frames") — the first consumers of `hart`/`node`. No
  current theorem needs them.

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
- **Modeled today.** *Mostly (S2.3 + SSG-3 device done).* `Machine.ipi` (per-core mailbox),
  `deliver_ipi`/`receive_ipi` transitions added, and "delivery precedes ack" proved
  (`hardware/rocq/ipi.v`: `receive_ipi_before_delivery_noop` — an undelivered remote
  cannot flush; `receive_ipi_after_delivery_sfences` — a delivered remote flushes
  its own core). The composed `ipi_broadcast` (invalidate the leaf PTE, deliver to,
  then receive from, every core) is proven to refine the functional
  `invalidate_shootdown` (`ipi_broadcast_refines_invalidate_shootdown`,
  `ipi_broadcast_correct`). The *device* that produces those delivered bits is
  modeled in `hardware/src/intc.sail` (a GIC-SGI / RISC-V-AIA-IPI subset:
  `intc_send`/`intc_mask`/`intc_unmask`/`intc_ack`), and `intc_proofs.v` proves
  send+ack refines `deliver_ipi` (`intc_send_ack_refines_deliver_ipi`) and a
  controller-produced mailbox flushes exactly core i
  (`intc_delivery_enables_receive_ipi`). **Primary-source cross-check done** —
  `doc/interrupt-controller.md` maps each stage to Arm IHI 0069 H.b (§1.2, §2.2.1,
  §4.4, §4.7.1) and RISC-V AIA (IPIs.adoc / IMSIC.adoc). telix's real mechanism is
  `broadcast_tlb_flush` (LAPIC vec 0xFC / PLIC).
- **Proof needed.** The remaining lift is the *device-in-the-loop Iris program* —
  the remote's flush gated on the controller's doorbell (send → pending → ack →
  doorbell) rather than the hand-set mailbox, composed with S2.2c's
  `bc_remote_spec`/`bc_wait_all_spec`. The ghost-level swap is now done:
  `intc_receive_ipi_eq_deliver` (intc_proofs.v) proves the controller's send+ack
  produces the same mailbox as `deliver_ipi`, so S2.4's per-step ghost
  `receive_ipi (deliver_ipi _ i)` is realized by the device. Also remaining:
  masking and interrupt context (SSG-3's other half). The per-core "delivery
  precedes ack" crux and the composed-broadcast refinement are done.

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

### SSG-9 — The grouping hierarchy: SMT threads up to NORMA clusters

- **Objective.** Span the machine's *grouping hierarchy* — **SMT threads → cores →
  NUMA nodes → small groups of near-adjacent NUMA nodes → SSI (Single System Image)
  shared-memory systems → distributed clusters with NORMA (No Remote Memory
  Access)** — and keep the kernel's notion of "which memory is local to which group"
  correct at every level.
- **Integrity.** Group-local memory never aliased across groups; cross-group state
  changes are message-passed, not shared. At the shared-memory levels (SMT/cores/
  NUMA/SSI), NUMA-aware algorithms that counter **starvation in lock-cacheline
  exclusive-access grants** (cacheline ping-pong / unfairness) are themselves part
  of what must be modeled and proven fair.
- **Modeled today.** *No — and note the homonym.* Tessera's "cluster" is **page
  clustering** (KAU = c·M), the project's core, modeled in the Lean Layer-A
  (`proof/Tessera/`) — not in the hardware model. The SSG-9 *distributed-cluster*
  sense is absent from both, apart from the flat per-core `Machine` list (an
  ungrouped set of cores).
- **Terminology (deliberately disambiguated).** Three senses of "cluster" collide;
  SSG-9 means only the last:
  1. **page clustering** (KAU = c·M) — Tessera's core, an *allocation-unit* notion,
     not a topology notion;
  2. **ccNUMA node — not a cluster.** A ccNUMA machine (even a multi-node one) is
     still a *tightly-coupled shared-memory* multiprocessor: one address space,
     real if non-uniform remote-memory access, i.e. an SSI — not a distributed
     cluster;
  3. **distributed-systems cluster** (SSG-9's sense) — a *loosely-coupled* set of
     independent machines over a network interconnect (Beowulf/HPC, datacenter
     clusters): the NORMA rung, message passing, no shared memory.
  In the classic distributed-systems taxonomy (tightly- vs loosely-coupled MIMD,
  Flynn 1972), shared-memory machines run UMA → ccNUMA → SSI, while "cluster"
  names the loosely-coupled message-passing pole; SSI is the attempt to make a
  cluster present as one shared-memory image. "group"/"node"/"domain" = the SSG-9
  topology hierarchy; "SSI" = single system image; "NORMA" = no remote memory
  access.
- **Proof needed.** Only if multi-node reasoning is taken on; ties into the domain
  remark below. The multikernel-domain boundary below is what makes the SSI/NORMA
  rungs of the hierarchy tractable — each rung is a message-passing refinement.

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

The same boundary recurs at every rung of the SSG-9 hierarchy: a multikernel domain
covers a NUMA node or a small group of near-adjacent nodes; an **SSI** system is a
group of domains presenting one shared address space (its cross-node coherence is a
scale-up of the intra-domain weak-memory argument); and a **NORMA cluster** is the
limit where there is no shared memory at all, so *every* cross-node interaction is
already message passing. The domain boundary is thus what carries the reasoning from
SMT threads cleanly up to distributed clusters.

## Sequencing

1. **SSG-2 (weak memory), concrete lift — in progress.** S2.2: the generated Sv39
   machine under gpfsl/ORC11.
2. **SSG-3 (IPI delivery)** — makes the shootdown proof real; follows SSG-2.
3. **SSG-1 (topology)** — `hart`/`node` fields are now on `Core` (the plumbing);
   remaining: topology-aware placement/affinity theorems, the first consumers.
4. **SSG-4 (IOMMU)** — self-contained replay of Stage 1/2.
5. **SSG-5–8 (devices)** — a scope expansion into I/O correctness, only if taken on.
6. **SSG-9 (grouping hierarchy: nodes → SSI → NORMA)** — only with multi-node reasoning; couples to the domain remark.

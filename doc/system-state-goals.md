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
- **Modeled today.** *Done (the concrete-machine lift landed).* The generated
  Sv39 walk + N-core broadcast is now proved under genuine weak memory
  (gpfsl/ORC11) over the *concrete* `machine.v`, not just an abstract boolean
  model. S2.2a–S2.2c (`shootdown_weak.v` → `shootdown_weak_broadcast.v`) prove the
  leader→remote PTE-invalidation ordering, the remote→leader ack, and their
  N-core composition; S2.4 threads the `Machine_ipi` mailbox through the
  weak-memory broadcast so the ghost step is `receive_ipi (deliver_ipi _ i)`;
  S2.5 composes the interrupt controller (`intc.sail`) into the program so the
  per-step ghost is the controller's send+ack. The toolchain blocker (separate
  `wm` switch) is resolved — gpfsl is vendored into `third_party/gpfsl` and built
  in the rocq-9.2 switch. See `stage2-shootdown.md`.
- **Proof needed.** Per-architecture instantiation of the parameterized memory
  model (`arch-coverage.md`); the VIVT/VIPT/PIPT distinction when cache models
  are added. The core weak-memory shootdown proof is complete.

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
  `receive_ipi (deliver_ipi _ i)` is realized by the device. **Masking +
  interrupt context done**: the model now distinguishes the per-interrupt enable
  (`masked` = inverted `eie`/`GICR_ICENABLER0`) from the per-hart delivery gate
  (`delivery` = `eidelivery`/`sstatus.SIE`); a hart in interrupt context holds
  its interrupt pending and takes it only on exit (`intc_ack_in_context_noop`,
  `test_vector_intc_exit_delivers`). **Interrupt priority selection modeled**
  (`hardware/rocq/intc_priority.v`): `topei` = the least eligible identity
  (`pending ∧ enabled ∧ below eithreshold`), with soundness/minimality/
  completeness/priority proved and `vm_compute` vectors pinning the picks.
  EOI/deactivation remain deliberate omissions (outside the shootdown-IPI
  subset). The per-core "delivery precedes ack" crux and the
  composed-broadcast refinement are done.

### SSG-4 — IOMMU / DMA controller

- **Objective.** Device translations (IOTLB) stay coherent with the CPU page table;
  DMA cannot reach a freed or remapped frame.
- **Integrity.** `IOTLB ⊆ mapping`, maintained by an IOMMU shootdown on every unmap.
- **Modeled today.** *Done.* `Machine_iotlb` + `IotlbEntry` + `iommu_walk` +
  `iotlb_invalidate` + `iommu_shootdown_correct` + `iommu_coherent` invariant +
  queued-invalidation command queue (`InvalidationCmd` / `iommu_process_queue` /
  `iommu_shootdown_via_queue`) + ATS device-TLB tier (`ats_invalidate` /
  `iommu_shootdown_ats_correct`) + ATS translation request/completion + PRI page
  request/servicing + VT-d context/PASID/scalable-device-table walks +
  PASID-cache coherence/eviction/refill + generation tags + FRCD fault recording
  + FRCDR drain + interrupt delivery of PRI faults + SMMUv3 two-stage walk +
  AMD-Vi 4-level walk + per-platform granularity/invalidation vectors — all
  modeled in `machine.sail` / `intc.sail`, proved in `iommu_proofs.v` /
  `vtd_proofs.v` / `smmu_proofs.v` / `amdvi_proofs.v`, and lifted to genuine weak
  memory (gpfsl) in `iommu_broadcast_weak.v` / `pasid_translate_weak.v` /
  `smmu_translate_weak.v` / `amdvi_translate_weak.v` / `ats_devtlb_weak.v` /
  `pri_fault_weak.v` / `pri_fault_intc_weak.v`.
- **Proof needed.** The `IOTLB ⊆ mapping` replay is *done* — every functional
  theorem and every weak-memory ghost lift is axiom-free and wired into
  `build.sh`. The model is cross-checked against VT-d 5.20 / SMMUv3 H.a /
  AMD-Vi 3.11 / PCIe 6.0 via conformance vectors (not full refinement). Remaining:
  a full derivation from upstream Sail IOMMU models (which do not yet exist as
  upstream artifacts), and the full command-queue/MMIO circular-wrap increment.
  Scoped in `doc/iommu-shootdown-plan.md` (S4.1–S4.5, all landed).
- **Primary source available.** `~/Dokumente/PCI-Express-6_0-Specification-PCIE_SIG.pdf`
  (PCIe Base Spec **Rev 6.0** — the user notes it is *only* 6.0, not 6.1/7.0).
  It is the device↔IOMMU *interface*: **ATS** (Address Translation Services —
  translation requests/completions, the IOTLB), **PRI** (Page Request Interface —
  device-side page faults), and **PASID/TLP prefixes** (shared virtual memory).
  The *IOMMU walker/invalidation* semantics themselves are now sourced too:
  `~/Dokumente/D51397-019-vt-directed-io-spec.pdf` (**Intel VT-d, Rev 5.20,
  April 2026**, order D51397-019). Relevant chapters for the `IOTLB ⊆ mapping`
  replay: §3 (domains + address translation — legacy §3.4.2 / scalable §3.4.3
  first-level+second-level), §6.2 (address-translation caches — context-cache
  §6.2.2, PASID-cache §6.2.3, **IOTLB §6.2.4**), §6.5 (invalidation of
  translation caches — the queued-invalidation descriptors: **IOTLB Invalidate
  §6.5.2.3**, PASID-based IOTLB §6.5.2.4, **Device-TLB Invalidate §6.5.2.5**, and
  the Invalidation-Wait descriptor §6.5.2.9 — i.e. the IOMMU shootdown), §4
  (ATS: invalidation request/completion §4.1.4, device-TLB invalidations §4.3),
  and §7 (address-translation faults + page-request handling §7.4.1 — the PRI
  side). So the replay reuses Stage 1/2 for the CPU side, ATS/PRI for the device
  side, and VT-d §3/§6.2/§6.5 for the IOMMU walker + invalidation, all on the
  same `IOTLB ⊆ mapping` invariant. The Arm cross-check is now sourced too:
  `~/Dokumente/IHI0070H_a-System_Memory_Management_Unit_Architecture_Specification.pdf`
  (**Arm SMMUv3, IHI 0070, version H.a = SMMUv3.5, March 2026**). Relevant
  chapters: §3.3 (stream-table lookup §3.3.1, StreamID→context descriptors
  §3.3.2, configuration + translation lookup §3.3.3 — the walker), §3.9 (PCIe,
  PASID, PRI, ATS — §3.9.1 ATS interface), §4 (command queue + invalidation:
  §4.3 configuration-structure invalidation, §4.4 TLB invalidation §4.4.1-4.4.4,
  §4.5 ATS and PRI), §5.2 (STE) / §5.4 (CD) data structures, §6.3.26-6.3.28
  (SMMU_CMDQ_* registers). The **AMD cross-check** completes the third platform:
  `~/Dokumente/48882_3.11_IOMMU_PUB.pdf` (**AMD I/O Virtualization Technology
  (IOMMU) Specification, Rev 3.11, April 2026**, order 48882, 313 pp). Relevant
  chapters: §2.2.2 (device table), §2.2.3 (I/O page tables for host translations
  — the walker), §2.2.6/§2.2.7 (guest/nested translations, incl. GPA→SPA sharing
  with the AMD64 page tables §2.2.4), §2.4 (command buffer — **INVALIDATE_IOMMU_
  PAGES §2.4.3**, **INVALIDATE_IOMMU_ALL §2.4.8**, ordering rules §2.4.11 — i.e.
  the IOMMU shootdown), §2.6 (peripheral page-request logging — the PRI side),
  and §2.11 (secure ATS support — the device-TLB side).

  **SSG-4 is now fully sourced on all three platforms**, so the `IOTLB ⊆ mapping`
  replay can be cross-checked three ways:

  | Platform | Walker + invalidation source | Device side |
  |---|---|---|
  | Intel | VT-d 5.20 §3/§6.2/§6.5 | PCIe 6.0 ATS/PRI + VT-d §4 |
  | Arm | SMMUv3 H.a §3.3/§4.4 | PCIe 6.0 ATS/PRI + SMMU §3.9 |
  | AMD | AMD-Vi 3.11 §2.2/§2.4 | PCIe 6.0 ATS/PRI + AMD-Vi §2.6/§2.11 |

### SSG-5 — Timer device(s)

- **Objective.** Timekeeping and the scheduler tick are correct against the device.
- **Integrity.** Tick accounting monotone/consistent across cores.
- **Modeled today.** *Yes* (2026-08-22): `timer.sail` (HartTimer + TimerDevice types), `timer_ops.v` (timer_tick, timer_set_mtimecmp, timer_ack, nth_hart, tick_harts), `timer_proofs.v` (5 headline theorems + 112 axiom-free test vectors (including descriptor wraparound, TX/RX independence) covering multi-hart, overflow, persistence, and ack-target isolation).
- **Proof needed.** None for the clustered-VM goal; only if driver/device-model
  correctness is taken on (a scope expansion).

### SSG-6 — Console device (UART)

- **Objective.** The console driver drives the UART correctly.
- **Modeled today.** *Yes* (2026-08-22): `uart.sail` (types), `uart_ops.v` (write_thr, tx_complete, read_rbr), `uart_proofs.v` (15 axiom-free test vectors (including flow-control, interrupt, two-char sequence, and scratch-register preservation)).
- **Proof needed.** Tx round-trip (write→tx_complete→read returns same character): done.

### SSG-7 — Network device

- **Objective.** NIC driver correct; buffers/descriptors not corrupted under DMA.
- **Modeled today.** *Yes* (2026-08-22): `net.sail` (DmaDesc + NetRegs types), `net_ops.v` (tx_pending, rx_pending, tx_advance_head, rx_advance_tail), `net_proofs.v` (12 axiom-free test vectors (including descriptor wraparound, TX/RX independence)).
- **Proof needed.** ~~DMA coherence via SSG-4 IOMMU~~ — **closed** (`net_dma_coherence.v`: ring_base_valid, tx/rx_advance_iommu_invariant, 4 axiom-free test vectors). Remaining: descriptor-offset translation (bitvector injection boundary).

### SSG-8 — Disk device

- **Objective.** Disk driver correct; swap/page-IO coherent with the mapping.
- **Modeled today.** *Yes* (2026-08-22): `disk.sail` (DiskCmd + DiskRegs types), `disk_ops.v` (cmd_pending, cmp_pending, cmd_submit, cmp_complete, is_read/write/flush), `disk_proofs.v` (20 axiom-free test vectors (including flush/barrier identification, cmd/cmp independence, ring-base preservation)).
- **Proof needed.** DMA coherence via SSG-4 IOMMU (same pattern as SSG-7); swap *data* discipline already covered in `proof/Tessera/Swap.lean`.

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

## Sequencing (updated 2026-08-21)

1. ~~**SSG-2 (weak memory), concrete lift — in progress.**~~ **Done.** S2.2a–S2.2c +
   S2.4 + S2.5: the generated Sv39 machine under gpfsl/ORC11, the IPI mailbox,
   and the interrupt controller, all proved axiom-free.
2. ~~**SSG-3 (IPI delivery)** — makes the shootdown proof real; follows SSG-2.~~
   **Done.** `ipi.v` + `intc.sail` + `intc_proofs.v` + `intc_weak_broadcast.v` +
   `shootdown_weak_broadcast_intc.v`: the full controller-in-the-loop weak-memory
   shootdown is proved, including masking, interrupt context, and priority selection.
3. **SSG-1 (topology)** — `hart`/`node` fields are now on `Core` (the plumbing);
   remaining: topology-aware placement/affinity theorems, the first consumers.
4. ~~**SSG-4 (IOMMU)** — self-contained replay of Stage 1/2.~~ **Done.** S4.1–S4.5:
   coherence, concurrent shootdown, ATS/PRI device side, three-platform port
   (VT-d / SMMUv3 / AMD-Vi), generation tags, and weak-memory lifts — all
   axiom-free.
5. ~~**SSG-5–8 (devices)** — a scope expansion into I/O correctness.~~ **Done.** Timer (SSG-5), UART (SSG-6), NIC (SSG-7), and disk (SSG-8) are all modeled with axiom-free test vectors. SSG-7 DMA coherence (ring_base ↔ IOMMU) is closed.
6. **SSG-9 (grouping hierarchy: nodes → SSI → NORMA)** — only with multi-node
   reasoning; couples to the domain remark.

**Current frontier:** the translation/coherence wedge (SSG-2/3/4) is complete.
Natural next steps are (a) the trust-line work — deriving the Tessera walk from
upstream `sail-riscv` / `sail-arm` rather than the hand-written conformance oracle
(see `rigor-trust-line.md` §5 G1), and (b) the first device track beyond the IOMMU
(SSG-5 timer or SSG-6 UART) or SSG-1 topology-aware theorems, depending on which
property next demands hardware-state reasoning.

# Kernel development plan

## Status: planning (2026-08-24)

This document records the high-level strategy for building the verified
Telix kernel atop the Tessera hardware model.  It complements
`stage3-kernel-strategy.md` (which covers the verification pipeline)
and the whitepaper (`~/src/telix-whitepaper/`, which covers the
design).  The focus here is *what code gets written, in what order,
and how the two prototypes relate*.

---

## 1. Two prototypes, one repository

The existing first-round prototype (`~/src/telix/`, Rust) is a
monolithic kernel that demonstrated page clustering, COW fork, demand
paging, and the shootdown protocol.  It is **frozen**: it stays in the
repo as a reference and a source of test harnesses, but new verified
code is not layered into it.

The second-round prototype is built **incrementally, component by
component**, beside the first in the same repository.  The verified
components cannot be structured the same way as the prototype's
monolithic VM — the framekernel/multikernel matryoshka, external
pagers, and continuation-passing style demand a different code
structure.  Building side-by-side lets the prototype guide the
redesign without being entangled by it.

The sketch below is the *intent* (prototype and second-round side by
side in one repo).  The **actual repository layout** (2026-08-25) is:
`kernel/` is the frozen prototype (it already owns that path and the
`telix-kernel` crate name), and the second-round kernel grows in a new
`kernel-v2/` crate next to it.  The repo/build mechanics of that split
(standalone cargo workspace, neutral-CWD build entry, host-testable
`no_std`-in-kernel crate) are recorded in Telix's
[`docs/kernel-v2-build-plan.md`](~/src/telix/docs/kernel-v2-build-plan.md)
— the planning here is authoritative for strategy/order; that document
is authoritative for the Telix-repo mechanics.

```
telix/
├── kernel/             ← first-round prototype (frozen), reference + harnesses
└── kernel-v2/          ← second-round, verified, built incrementally (OWN workspace)
    ├── src/caps/       ← K1.5: capability transport (done, host-tested)
    ├── framekernel/    ← K2: page tables, shootdown, IPI, IOMMU
    ├── allocator/       ← K3: LLFree (lock-free, coremapless)
    ├── pagers/          ← K7-K8: external pagers (COW, ZFOD, page cache)
    ├── personality/    ← K9: Linux, Windows, Zircon, OpenHarmony servers
    └── drivers/        ← K10: device drivers (userspace, untrusted)
```

---

## 2. Build-up order

The order is dictated by what the verification pipeline can support at
each stage, not by what would be fastest to boot.

| Phase | Component | Lines (est.) | Verification | Dependency |
|-------|-----------|-------------|--------------|------------|
| **K1** | Machine interface Iris layer | ~2,000 Rocq | Proved against Tessera machine model | Tessera hardware proofs (done) |
| **K1.5** | Capability transport (cap table, ports, message passing) | ~900 Rust + Iris spec | Manual Iris against K1 resources (decided 2026-08-25; Rust host-tested in `kernel-v2/src/caps/`) | K1 |
| **K2** | Framekernel core: PTE walk/modify, sfence.vma, IPI send/recv | ~1,500 Rust | Manual Iris against K1 resources | K1 |
| **K3** | LLFree allocator (lock-free, coremapless) | ~1,000 Rust | Manual Iris (or trusted primitive) | K1 |
| **K4** | TLB shootdown protocol implementation | ~500 Rust | Manual Iris composing K1 + S2 theorems | K1, K2 |
| **K5** | IOMMU management (IOTLB invalidate, ATS/PRI) | ~800 Rust | Manual Iris composing K1 + S4 theorems | K1, K2 |
| **K6** | Scheduler management loop (EEVDF, per-core) | ~1,200 Rust | Manual Iris (bounded state) | K2 |
| **K7** | External pager framework (capability channels, fault dispatch) | ~1,000 Rust | Protocol-level (K1 contracts) | K2, K4 |
| **K8** | First external pager: COW + ZFOD | ~800 Rust | Independent Iris proof | K7 |
| **K9** | First personality server: Linux POSIX | ~2,000 Rust | Untrusted (capability protocol only) | K7, K8 |
| **K10** | Device drivers: UART, timer, NIC, disk | ~1,500 Rust | Untrusted | K7 |

Total framekernel core (K2–K6): ~5,000 lines of Rust — matching the
whitepaper's estimate.  This is the verification target.

---

## 3. Verification strategy (summary)

The detailed pipeline is in `stage3-kernel-strategy.md`.  The key
decision, updated to match the whitepaper:

**Manual Iris heap_lang is the chosen path**, not RefinedRust.
RefinedRust was considered (and is surveyed in the stage3 doc) but
rejected because its bare-metal compatibility (no `std`, raw MMIO,
inline assembly, custom allocator) is unproven.  The kernel spec is
written by hand in Iris heap_lang, in the style of seL4's Isabelle
specification, and proved against the machine interface resources
from K1.

The `stage3-kernel-strategy.md` document still references RefinedRust
as the chosen tool (15 mentions).  That document should be updated to
reflect the manual-Iris decision.  The survey of Rust→Coq tools
remains valuable as a rationale for *why* manual Iris was chosen.

---

## 4. Relationship to the hardware model

The hardware model (Stages 1–2, SSG-1–9) is **complete**.  All
machine-side theorems are axiom-free and machine-checked in Rocq.
The kernel build-up depends on:

- **K1** consumes `bc_broadcast_spec`, `coherence_leaf`,
  `iommu_shootdown_correct` and the machine-interface Iris resources.
- **K4** composes the S2 weak-memory shootdown theorems.
- **K5** composes the S4 IOMMU coherence theorems.
- **K6** uses the SSG-3 interrupt controller model for IPI delivery.
- **K7** uses the SSG-1 topology model for cross-domain shootdown scoping.

No further hardware-model work is blocking the kernel build-up.
The trust line (G1: upstream Sail conformance) is substantially
advanced; the remaining gap (full upstream generation for all
architectures) can proceed in parallel with K1–K2.

---

## 5. Test strategy

- **Unit tests**: each kernel component gets QEMU-based tests that
  exercise the protocol paths (PTE modify, shootdown, IPI, IOMMU
  invalidate).
- **Conformance diff-test**: the kernel's page walks are compared
  against Tessera's `oracle_walk` in QEMU, catching any divergence
  from the hardware model.
- **PMC tracing**: Phase 3.3 of the stage3 strategy — lightweight
  runtime assertions that the protocol is being followed, checked
  offline against the protocol contracts.
- **Axiom hygiene**: the Tessera build script checks for axiom leaks;
  the kernel proofs will use the same check.

---

## 6. Open questions

1. **Prototype code reuse**: how much of the first-round prototype's
   Rust code can be directly reused vs. rewritten?  The page-clustering
   math is reusable; the VFS/VM coupling is not.

2. **Assembly specialisation**: the whitepaper says privileged
   instructions (`sfence.vma`, `mret`, `csrw satp`) are specialised
   from the Sail machine model.  This needs a concrete Sail→Rust
   extraction path, or hand-written assembly with Iris specs.

3. **Scheduler verification scope**: the EEVDF management loop is
   TCB code, but the user-facing EEVDF fairness proofs are a
   separate (and hard) problem.  The initial target is just the
   protocol-relevant paths (K2–K6); full scheduler fairness is
   deferred.

4. **External pager independence**: each pager gets its own proof,
   but the capability-channel protocol between pager and framekernel
   must be verified first (K7).  This is the dependency that gates K8+.

5. **K1 minimal subset for K1.5**: the capability-transport spec needs
   only a slice of the machine interface (memory/alloc resources,
   gpfsl for the lock-free rings, the intc wakeup ghost step, SSG-1
   scoping).  Recommended: define the minimal K1 subset first so K1.5
   is not blocked on the full ~2,000-line K1 layer.

6. **Ring refinement scope**: the port queue's lock-free-ring
   refinement (gpfsl) is a later milestone; confirm it stays out of
   K1.5's initial scope.

7. **Transport wakeup path**: cross-partition `recv` blocking + IPI
   wakeup composes with the SSG-3 theorems (`bc_machine_ipi_step_via_
   intc`); the concrete spec for it is a K1.5 follow-up.

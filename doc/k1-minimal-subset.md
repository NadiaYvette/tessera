# K1 minimal subset — the machine-interface contract for K1.5

Status: **contract agreed; Layer-A model landed (2026-08-25)**.
Companion to `doc/kernel-development-plan.md` (K1–K10 build-up) and
`doc/stage3-kernel-strategy.md` (the pipeline).  This document pins
down the **minimal K1** the capability transport (K1.5) needs, so K1.5
is not blocked on the full ~2,000-line machine-interface layer, and it
records the framekernel structuring discipline that governs what is
absorbed into the kernel core and what stays outside.

Since this contract was written, the pure Layer-A model
(`hardware/rocq/cap_transport_model.v`, §4) has been written and wired
into `build.sh` with its headline theorems axiom-free (17 checks in the
`cap_transport_model` group); the kernel-side doorbell + cluster are in
`~/src/telix/kernel-v2/src/caps/` (39 host tests green).  The next step
remains the Iris heap_lang spec against this contract.

## 1. Framekernel structuring (the matryoshka discipline)

The user's guiding principle (2026-08-25): the absorption of
functionality into the kernel for efficiency must be **structured and
disciplined** by the framekernel idea.  In matryoshka terms, each layer
absorbs only what earns its place:

| Layer | What lives there | Why it is (or is not) absorbed |
|---|---|---|
| **Kernel core proper** (this work) | Capability transport: cap table, ports, message passing, and the narrow doorbell-IPI read/write | The microkernel heart (seL4 lesson: IPC + cap table is the core). No policy — pure mechanism. |
| **Doorbell device interface** (absorbed) | The minimal `pending / masked / delivery` doorbell read/write against the interrupt controller | Only the *wakeup mechanism* is absorbed into the core, behind a narrow interface. The full INTC semantics stays in the hardware model (`intc.sail`, verified in Tessera) and the device layer. |
| **Memory management** (NOT absorbed yet) | Pagers, allocation policy, page-table manipulation | "Tremendously more intricate" — deliberately deferred until the connecting pieces (capability channels over which pagers will talk) exist. The kernel core provides primitives; userspace servers compose them. |
| **Personalities, drivers, filesystems** (outside) | Userspace servers | Untrusted by construction; capability-channel protocols only. |

The capability transport is the right first kernel-code step precisely
because it is the **connecting tissue**: every other component (pager,
scheduler, personality) will talk over capability channels.  Getting
its ownership and gating semantics right first de-risks everything
above it.

## 2. What the capability-transport spec consumes

`cap_transport_iris.v` is a heap_lang program spec.  Its `wp` triples
mention exactly four resources.  **Minimal K1 = these four, and nothing
more:**

### 2.1 Memory/alloc resources — for the cap table and port records

- **Need:** a way to allocate the memory backing a task's capability
  table and a port's queue, and a way to state ownership of that memory
  in Iris.
- **K1 must provide:** a `cap_table_own` / `port_own` style resource —
  in the simplest form, a named ownership predicate over a range of
  machine memory, allocated by the kernel core and never exposed to
  tasks.  (The full frame/allocator interface of the eventual K1 is
  out of scope; only the ownership resource is needed.)
- **The port queue refinement note:** the Iris spec states the port as
  a *bounded FIFO queue* (abstract representation).  The whitepaper's
  lock-free rings are the concrete representation, connected by a
  refinement under gpfsl — the same Layer-A/Layer-S pattern Tessera
  already uses for extent tiling.  That refinement is a later
  milestone (open question 6 in `kernel-development-plan.md`), not part
  of minimal K1.

### 2.2 gpfsl — only if a shared-memory primitive is in the spec

- **Need:** none for the *queue* operations themselves (they are
  kernel-core, single-threaded over owned memory).  gpfsl enters only
  where a lock-free ring or a shared flag crosses a trust boundary.
- **K1 must provide (later, not minimal):** the gpfsl (iRC11) resources
  matching `shootdown_weak_broadcast.v`'s release/acquire pattern, when
  the ring refinement lands.  Minimal K1 can be plain Iris (iRC11
  sequential) — this is a deliberate simplification, recorded here so
  the later lift is a known, scoped step.

### 2.3 The intc wakeup ghost step — for cross-partition delivery

- **Need:** cross-partition `recv` blocking and IPI wakeup.
- **K1 must provide:** a ghost step that reifies the doorbell: the
  delivery of an IPI to a partition's controller and the resulting
  wakeup of a blocked recv.  **This exists already in Tessera**:
  `intc_weak_broadcast.v`'s `bc_machine_ipi_step_via_intc` proves the
  S2.4 weak-memory broadcast's ghost step *is* the controller's
  send+ack.  Minimal K1 adapts that pattern: the transport's
  cross-partition send = enqueue + doorbell `deliver`; the kernel
  core's wakeup read = `pending && !masked && delivery` (the same
  preconditions `bc_machine_ipi_step_via_intc` states).
- **Consumed theorems:** `bc_machine_ipi_step_via_intc`,
  `bc_machine_ipi_step_via_intc_cores` (module `intc_weak_broadcast`),
  and the `intc_proofs.v` lemmas (`intc_receive_ipi_eq_deliver`).

### 2.4 SSG-1 topology scoping — for the multikernel partition map

- **Need:** knowing which partition owns a port, i.e. the
  partition→port routing map.
- **K1 must provide:** a `port_owner : PortId -> PartitionId` map as
  ghost state, constrained by the SSG-1 topology model (domains are
  the natural multikernel boundaries).  Minimal form: a well-formed
  `port_owner` map + the "a send crosses a domain boundary iff
  `owner(sender) ≠ owner(port)`" lemma.  The topology model itself
  (`topology.v`, `placement.v`) is already proven; K1 consumes it.

## 3. The minimal K1 interface (signature sketch)

In Rocq, minimal K1 is a module (in `hardware/rocq/`) exposing:

```coq
(* ghost resources *)
Parameter cap_table_own : TaskId -> gname -> iProp.   (* shape only *)
Parameter port_own     : PortId -> list Message -> iProp.
Parameter port_owner   : PortId -> PartitionId -> Prop.  (* SSG-1-constrained *)

(* the doorbell wakeup predicate, mirroring intc_weak_broadcast *)
Definition doorbell_wake (part : PartitionId) (port : PortId) : Prop :=
  pending part port /\ ~ masked part port /\ delivery part port.
```

with the wp triples for `alloc_slot`, `free_slot`, `grant`,
`create_port`, `send`, `recv` stated over these resources (the full
list is in `doc/kernel-development-plan.md` K1.5 and the Telix bridge
doc `~/src/telix/docs/kernel-v2-verification-bridge.md`).

## 4. What this session delivers

- This contract (this document).
- `hardware/rocq/cap_transport_model.v` — a **pure Coq Layer-A model**
  (no Iris): the cap table, ports, and the cap-gating predicate with
  the invariants proven axiom-free (`send_never_drops`, `recv_fifo`,
  `grant_no_amplification`, `cap_unforgeable`).  This is the
  specification the Iris spec will state; proving it pure-first
  de-risks the heap_lang version, exactly as Tessera's Layer-A Lean
  proofs precede the machine-level work.
- The kernel-side cross-partition recv model in Telix `kernel-v2`
  (doorbell + cluster), which is the *behavioral* counterpart of §2.3.

The Iris heap_lang spec (`cap_transport_iris.v`) is the next step,
written against this contract once minimal K1 lands.

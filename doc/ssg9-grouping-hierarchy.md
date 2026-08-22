# SSG-9: The Grouping Hierarchy — SMT Threads to NORMA Clusters

## 1. Overview

SSG-9 spans the machine's *grouping hierarchy* from the finest to the coarsest
level of hardware organization:

```
SMT threads → cores → NUMA nodes → small NUMA groups → SSI → NORMA clusters
```

The kernel must maintain the invariant that **group-local memory is never
aliased across groups**, and that cross-group state changes are message-passed,
not shared.

## 2. Terminology (deliberately disambiguated)

Three senses of "cluster" collide; SSG-9 means only the last:

1. **Page clustering (KAU = c·M)** — Tessera's core, an *allocation-unit*
   notion, not a topology notion. This is the project's novel contribution
   (Dickins 1995, Chambers 2003).

2. **ccNUMA node — not a cluster.** A ccNUMA machine is still a
   tightly-coupled shared-memory multiprocessor: one address space, real
   if non-uniform remote-memory access, i.e. an SSI — not a distributed
   cluster.

3. **Distributed-systems cluster (SSG-9's sense)** — a loosely-coupled set of
   independent machines over a network interconnect (Beowulf/HPC, datacenter
   clusters): the NORMA rung, message passing, no shared memory.

In Flynn's 1972 taxonomy: shared-memory machines run UMA → ccNUMA → SSI,
while "cluster" names the loosely-coupled message-passing pole.

## 3. Topology as a verification boundary

### 3.1 Multikernel domains (Barrelfish-like)

**NUMA nodes — or small groups of near-adjacent NUMA nodes — are the natural
boundary for Barrelfish-like multikernel domains.** A domain owns its
node-local memory and a private kernel instance; communication *between*
domains is explicit message passing, not shared mutable kernel state.

This is not only an OS-structure choice — it is a **verification-scoping**
choice:

- **Within a domain** the cores share memory, so the full weak-memory
  burden of SSG-2/SSG-3 applies (the gpfsl/ORC11 proofs in
  `property2/`).
- **Across domains** communication is message passing, a stronger and
  simpler abstraction — so the relaxed-memory reasoning is *concentrated
  inside* the domain, and the cross-domain link is discharged by a
  message-passing refinement rather than a raw shared-memory argument.

### 3.2 Framekernel within a domain (Asterinas-like)

**Within one such domain, the Asterinas-like framekernel method is worth
employing to cut IPC overhead.** A single shared kernel address space
across the domain's cores, with per-core state separated and cross-core
access mediated (and proven race-free), so the bulk of communication is
ordinary function calls and shared memory rather than IPCs.

The framekernel boundary separates:

- **Kernel-core code** (runs in kernel mode, accesses all memory):
  scheduler, VM subsystem, DMA setup, interrupt handling.
- **User processes** (run in user mode, access only their own pages):
  applications, libraries, system servers.

This maps directly to the Tessera verification layers:

| Layer | Scope | Weak-memory burden |
|-------|-------|-------------------|
| SSG-2 (gpfsl) | Intra-domain cores | Full ORC11 |
| SSG-3 (IPI) | Intra-domain cross-core | Release/acquire |
| SSG-4 (IOMMU) | Intra-domain DMA | IOTLB ⊆ mapping |
| SSG-9 (domain) | Inter-domain | Message-passing refinement |

### 3.3 The hierarchy carries upward

The same domain boundary recurs at every rung:

- **SSI** = a group of domains presenting one shared address space.
  Its cross-node coherence is a scale-up of the intra-domain
  weak-memory argument.
- **NORMA cluster** = the limit where there is no shared memory at
  all, so *every* cross-node interaction is already message passing.

The domain boundary is thus what carries the reasoning from SMT threads
cleanly up to distributed clusters.

## 4. Modeling the hierarchy in Tessera

### 4.1 Current state

The `Machine` record is currently a flat `list Core` — an ungrouped set
of cores. Node/hart grouping is absent from the hardware model.

### 4.2 Target: grouped Machine

The `Machine` record should gain:

```ocaml
Record Node := {
  node_id    : Z;
  node_cores : list Core;
  node_mem   : list MemEntry;   (* node-local memory *)
}.

Record Domain := {
  dom_id    : Z;
  dom_nodes : list Node;
  dom_ipc   : list Message;     (* inter-domain message queue *)
}.

Record Machine := {
  mach_domains : list Domain;
  mach_global  : list MemEntry;  (* shared-memory only if SSI *)
}.
```

### 4.3 Verification obligations

At each rung of the hierarchy:

| Rung | Obligation | Tessera artifact |
|------|-----------|-----------------|
| SMT threads | Co-resident threads share no private TLB state | SSG-1 topology |
| Cores | Cross-core shootdown is sound under weak memory | SSG-2/3 (done) |
| NUMA nodes | NUMA-local allocation never aliases remote frames | Future |
| NUMA groups | Group-local DMA through IOMMU is coherent | SSG-4 + SSG-7/8 |
| SSI | Cross-domain coherence via message-passing refinement | Future |
| NORMA cluster | Every interaction is message-passing by construction | Axiom |

### 4.4 Lock-fairness under NUMA

At the shared-memory levels (SMT/cores/NUMA/SSI), NUMA-aware algorithms
that counter **starvation in lock-cacheline exclusive-access grants**
(cacheline ping-pong / unfairness) are themselves part of what must be
modeled and proven fair.  This is the LCR (Latent Critical Region) problem:
a cacheline grant can be delayed indefinitely under contention, leading to
starvation without an explicit timeout or fairness mechanism.

The Tessera approach:

1. Model cacheline state as ghost state in the gpfsl proof.
2. Prove that a fairness-aware spinlock (e.g., ticket lock or MCS lock)
   satisfies the starvation-freedom property.
3. Compose with the shootdown proof to show the full protocol remains
   correct even under unfair cacheline access.

## 5. Sequencing

SSG-9 is the *last* rung of the hierarchy to be modeled, because it
requires:

1. A working multi-domain Machine (Step 4.2 above).
2. A message-passing abstraction between domains.
3. A refinement proof showing cross-domain communication is equivalent
   to message passing.

The current focus (SSG-2 through SSG-8) builds the foundation for a
*single* domain.  SSG-9 will compose these single-domain results into
a multi-domain system.

## 6. Open questions

1. **How many NUMA nodes per domain?**  The optimal grouping depends on
   the interconnect topology (e.g., Intel Mesh, AMD Infinity Fabric).
   Should this be a kernel command-line parameter?

2. **Cross-domain page migration:**  When a process migrates between
   domains, its page tables must be reconstructed.  Is this modeled as
   a DMA-like operation or as a message-passing primitive?

3. **SSI coherence protocol:**  For SSI systems, is the cross-node
   coherence a MESI/MOESI variant, or is it purely software-managed
   (e.g., through a distributed TLB shootdown)?

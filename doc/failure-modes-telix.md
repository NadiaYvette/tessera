# telix — memory-management failure-mode catalog

**Purpose.** MM bugs that actually occurred during telix development (the
from-scratch microkernel that originated the clustered-superpage design), mapped to
the Tessera invariants (see `tessera-verification-kickoff.md`). The empirical threat
model: what the proof must rule out, and which invariants carry the risk. Mined
read-only from telix docs (`wild-rip-mechanism.md`, `slab-pt-va-isolation.md`,
`scheduler-race-investigation.md`), the ~1231-commit git history, and the Claude
session transcript + ~266 `memory/project_*.md` root-cause notes under
`~/.claude/projects/-home-nyc-src-telix/`.

**Telix already contains the Layer-A operation set the proof targets:**
`mm/extent.rs` (`split_at`), `mm/vmatree.rs` (VMA split/merge), `mm/cowgroup.rs` +
`mm/ptshare.rs` (COW sharing groups, PT-node refcounts), `mm/radix_pt.rs`
(`cow_break_table`, `ensure_path_unshared`, `free_shared_subtree`), `mm/hat.rs` +
`arch/x86_64/mm.rs` (`map_range`, `unmap_single_mmupage`+`invlpg`,
`demote_superpage`, `clone_shared_tables`), `mm/aspace.rs` (`unmap_range`). Cross-CPU
`broadcast_tlb_flush` (LAPIC vec 0xFC) exists but is wired only into the
write-protect/demote paths, not general unmap.

Top transcript signatures (whole-file counts): `wild-rip` ~21.7k, `overlap` 16.4k,
`use-after-free` 5.7k, `double-free` 3.3k, `tlb shootdown` 3.1k, `guard page` 3.5k,
`superpage` 2.5k, `demote`/`promote` ~4.4k/0.75k, `premature-free` 333, `cow break`
35, `stale tlb` 35.

## A) Catalog

| # | Title | Symptom | Root cause | File / commit | Category | Invariant/Property + layer |
|---|---|---|---|---|---|---|
| 1 | Fork COW-marks kernel PML4 slots | deterministic triple-fault after first `fork` | `clone_shared_tables` looped `1..512`, turning kernel-half VA-isolation entries PML4[507..511] into COW "shared markers"; next fault/IRQ can't reach rsp0 → #DF→triple | `arch/x86_64/mm.rs::clone_shared_tables` (`015c485`) | COW / extent-overlap | **inv2 + inv6**; COW-share relation must exclude kernel extents. Layer A |
| 2 | Aspace teardown frees globally-shared Thread L2 | aarch64 EL1 translation faults in scheduler | `free_page_table_tree` freed the shared `SLAB_THREAD_REGION` L2 installed in every aspace; pages reused → every Thread VA unmapped | aarch64 free path (`8e7630e`) | UAF / refcount (shared node) | **inv6 + inv2**; shared PT subtree reclamation must be refcounted. Layer A/I |
| 3 | PT teardown UAF vs live TTBR0 (no grace period) | aarch64 ~2/3 boots: EL1 Data Abort walking a dying aspace | `aspace::destroy` freed the PT tree while another CPU held that aspace in TTBR0 | `mm` teardown / `sync/rcu.rs` (`63720b2`) | UAF / lifecycle race | **Property 2** (concurrent observation) — *out of sequential scope*; RCU-defer fix |
| 4 | RCU premature reclaim → ART/slab UAF | `SCHED_THREAD_ART` header scribble under pressure | `rcu_defer_free` stamped a batch's epoch once and never re-stamped on append; late node freed before grace period while a lock-free reader walked it | `sync/rcu.rs` (`b9bf8f4`) | UAF / epoch race | **Property 2** (grace-period ordering) — out of scope; loom-proven |
| 5 | Silent partial mapping (ignored map result) | userspace #PF mid-PCI-enumeration (riscv64 ECAM) | `sys_mmio_map_cap` looped `map_single_mmupage` and ignored its `bool`; a mid-loop PT-alloc OOM left a partial mapping, no rollback | `syscall/handlers.rs`, `mm/hat.rs` (`15b2772`,`5335f11`) | partial-population / atomicity | **Property-1 map postcondition**: success ⇒ whole extent present; failure ⇒ rolled back. Layer A |
| 6 | 9 more silent-partial-map sites | latent partial mappings → user #PF | same loop-and-ignore pattern in ELF loader, spawn stacks, anon mmap, execve stack, TLS | `loader/elf.rs`, `sched/scheduler.rs`, `syscall/*` (`5335f11`) | partial-population / atomicity | **Property 1** map-postcondition (a class) |
| 7 | Native mmap skips COW-break of shared PT markers | `discovery_srv` mmap fails `OutOfMemory` → #BR + #GP | native `mmap` went `map_anon→map_range` without `ensure_path_unshared`; after fork the PT carries shared markers → `walk_or_create` returns None | `syscall/handlers.rs`, `mm/hat.rs` (`e66ba2b`) | COW / partial-population | **inv6**: install into a COW-shared extent must break sharing first. Layer A precondition |
| 8 | Split VMAs sharing an object → free UAF | UAF when one of two split VMAs sharing an object is unmapped | `unmap_anon` destroyed the shared backing object without checking `mapping_count()`; sibling kept a dangling ref | `mm/aspace.rs::unmap_anon` (`39742c0`) | refcount / split-merge / UAF | **inv4 + inv6** (refcounts reflect sharing). Layer A/I |
| 9 | mprotect/mremap must demote + flush | stale superpage / stale TLB after a protection change | mprotect rewrites leaf PTE flags → must split VMAs at boundaries, **demote superpages**, **invalidate TLB**; mremap-shrink must unmap excess PTEs | `mm/aspace.rs` mprotect/mremap (`39742c0`) | demotion + stale-TLB + split | **inv3** forces demotion; **inv7/Property 1** forces the flush; **inv4** the split. Layer A (canonical multi-invariant op) |
| 10 | Shared-PT wprot demote needs cross-CPU shootdown | 0 `PF-WPROT-HIT` despite arming write-protect | local PTE wprot without a shootdown leaves remote CPUs on stale entries; fix added `broadcast_tlb_flush` after RW=0 | `arch/x86_64/{mm,lapic}.rs` (`756e9b9`) | stale-TLB (cross-CPU) | **inv7**; sequentially **Property 1** (invalidate at all), cross-CPU **Property 2** |
| 11 | Phys allocator double-issue (write-before-CAS) | "cafe-fault": one physical page handed to two owners → kstack PA aliasing | `chunk_alloc_one` wrote the bitmap before the publishing CAS; the loser's stale write clobbered the winner → double-issue | `mm/phys.rs` (`93be952`,`77cde8e`) | extent-overlap (phys) / CAS race / double-alloc | **inv1** (disjoint extents) at the physical layer; mechanism is **Property 2**. loom-proven |
| 12 | Deferred-kstack single-slot overwrite leak | Phase-5 spawn wedge: ~1 GB leaked over ~1000 exits → OOM | one per-CPU slot held one pending kstack PA; rapid same-CPU exits overwrote the prior pending PA, leaking it | `sched/scheduler.rs` (`ebbc5bb`) | leak / free accounting | Outside VMM algebra (allocator bookkeeping); relates to **inv2** reclamation. Layer I |
| 13 | Cross-data-structure scribble (no VA isolation) | `Thread.saved_sp` mutated by an untracked writer | slab/PT/kstack domains shared one VA space with no guard regions, so a stride bug in one wrote into another | `slab-pt-va-isolation.md`; x86_64 VA regions (`09cb0d4`,`a6c1db8`) | extent-overlap (kernel VA) | **inv1** (disjoint, aligned extents) for kernel objects; guards = the unmapped gaps inv1 implies. Layer A/I |
| 14 | Wild-RIP from zero-filled kstack | kernel #PF fetching from `0x0`,`0x19`,… (Rust line numbers as addresses) | `core::fmt` read a `u32`-only-written stack slot as `u64`; zero upper bytes made a usable small pointer. Mitigated by `0xCAFEBABE…` sentinel fill | `sched/scheduler.rs` (`9e9c4af`); `wild-rip-mechanism.md` | uninitialized-memory | **Outside the model** — language/codegen + uninit-fill, not a mapping invariant. Mitigation only |
| 15 | Stack-slot-overlap / concurrent wild write (#208 Family-3) | `alloc_kstack`'s own sret slot clobbered with small value | a wild 32-bit writer scribbles in-use kstack memory; suspected LTO stack-slot reuse and/or cross-CPU write | `sched/scheduler.rs` (`project_256_*`) | spatial corruption / race | partly **Property 2**, partly **outside model** (compiler stack-slot aliasing) |
| 16 | Double-dispatch via blind on_cpu publish | tid running on two CPUs → #PF RIP=0x0 | `dequeue_set_pending` stored `on_cpu=PENDING` over a real-cpu lease; claim CAS succeeded on a thread still executing | `sched/scheduler.rs` (`40d333c`,`47b9650`) | scheduler state-machine race | **Property 2**; not VMM, but the dominant *producer* of MM corruption (kstack reuse) |
| 17 | Page fault races aspace teardown | `aspace 6233 not found @ fault.rs:91` | `handle_page_fault` used `with_aspace` (panics) not `with_aspace_mut`; a fault outlived its aspace | `mm/fault.rs` (`7548370`) | lifecycle / UAF | **Property 2** for the race; handler must tolerate a removed aspace |
| 18 | Identity-map / phys-pointer deref fragility | corruption when raw PAs dereferenced after PML4[0] unmap | kernel dereferenced PAs as pointers via the identity map; removal required routing all PT-walks through `PHYS_DIRECT_MAP` | `mm/*` (`3a33dae`,…) | dangling/aliasing (phys vs VA) | Layer-I representation discipline; trusted-HW adjacent |
| 19 | Orphaned shared-PT marker (latent) | guarded (0×): a shared marker with null `fork_group` → later map silently fails | a COW shared marker left without an owning fork-group → `ensure_path_unshared` can't break it | `mm/hat.rs` (`91cad29`) | COW / refcount-consistency | **inv6**: every shared marker ↔ a live sharing group with consistent refcount. Layer A/I |
| 20 | Shared PT page vs object-boundary "overhang" | (design hazard) shared-PT refcount when a node spans VMA/object boundaries | a shared PT node can cover ranges from >1 VMA/COW-group; naïve per-object refcounts mis-account it | `feedback_pt_refcounts.md`; `mm/ptshare.rs` | refcount / alignment / COW | **inv2 + inv6** interaction: PT-node sharing granularity need not align to extent boundaries — a §3 modeling decision to make explicit |

## B) Ranked priorities

1. **Unmap/mprotect without complete TLB invalidation (#9,#10).** The brief's canonical case (Property 1 / inv7). [**Proven for unmap: `Tlb.lean`.**]
2. **Non-atomic map → partial population (#5,#6).** The most common real MM bug class here (10+ sites). The map op postcondition must be all-or-nothing.
3. **COW-break / shared-PT consistency (#1,#7,#19,#20).** Kernel extents wrongly shared, missing pre-write break, orphaned markers, boundary overhangs — **inv6** + the brief's explicit COW-with-superpages precondition.
4. **Refcounted reclamation of shared extents/PT nodes (#2,#8).** Freeing a shared object/subtree while referenced — **inv6 + inv4**, sequential.
5. **Superpage demotion forced by permission/partial change (#9).** Demote-before-protection-change — **inv3** is the precondition making the demotion provable.
6. **Physical extent disjointness under the allocator (#11).** Double-issue = two extents claiming one frame = **inv1** at the physical layer.

## C) Coverage vs. the brief's scope

- **In scope for sequential M1–M3:** #1,#7,#8,#19,#20 (COW/shared-extent consistency, split/merge — inv1/2/4/6); #5,#6 (map atomicity as an all-or-nothing postcondition); #9,#10 partial + the general unmap obligation (**Property 1 / inv7** — *the §4 obligation, now proven for unmap*); #11 stated as inv1.
- **Inherently Property 2 (deferred to litmus/loom):** #3, #4, #10's remote-observation half, #11's CAS mechanism, #16, #17. Telix validates several of these with **loom** models (`tests/loom-art-rcu-reclaim`, `loom-phys-chunk`, `loom-dispatch-compose`) — its de-facto Property-2 layer.
- **Outside the model (trusted / non-VMM):** #14 (uninit-fill + codegen), #15 (LTO stack-slot aliasing), #18 (PA-as-pointer representation), #12 (allocator accounting). #13 (kernel-VA isolation) is modelable as inv1 but the bug was a wild C-style write the type-level model assumes away.

**Net:** the MM bugs cluster almost exactly onto the brief's invariants. The sequential layer (inv1–6 + the inv7 obligation-to-invalidate) catches/structurally-prevents #1,#5–9,#19,#20 and the invariant statements of #11/#13 — the majority of distinct, non-residual defects. The heavy weak-memory hitters (#3,#4,#11-mechanism,#16) are correctly walled into Property 2 / loom / litmus, confirming the scoping. The one class the model *cannot* see — uninitialized-fill and compiler stack-slot wild writes (#14,#15) — is also the one telix could only *mitigate*, exactly the category §4 warns a pure-data proof cannot see.

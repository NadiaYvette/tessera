# PGCL #143 ↔ Tessera bridge (CBMC findings for the Lean/Kani effort)

Hand-off from the pgcl-side CBMC modeling of #143 to the Tessera verification
project (`~/src/tessera`). Tessera already catalogs #143 as item **#1** in
`doc/failure-modes-pgcl.md` and scopes the concurrent teardown-vs-walk race to its
**Property 2** track (`Teardown.lean` header). This updates that mapping with what
the CBMC models + an exhaustive code audit have since established, and states the
engine correspondence so the two efforts reinforce instead of duplicating.

## How the two shells collaborate (mechanism)
- **Shared filesystem.** Both `~/src/pgcl` and `~/src/tessera` are on one box; the
  Tessera shell already mines `~/src/pgcl/` read-only. So: pgcl keeps producing
  findings under `rmap-ab/formal/`, `docs/143-notes/`, `RMAP-DEBUG-TOOLKIT.md`
  (all pushed to the same 4 mirrors Tessera uses); Tessera ingests them.
- **Human bridge.** The user runs both shells and relays intent; this file is the
  explicit artifact so the relay is lossless.
- **Shared engine.** Tessera's `rust/extent-kani/` uses **Kani**, which is **CBMC**.
  The pgcl-side models in `rmap-ab/formal/*.c` are CBMC C. Same bounded-model-checker
  → a pgcl model can be reborn as a Kani harness in `rust/`, and Tessera's Lean
  theorems are the unbounded (∀N) complement of the pgcl bounded checks.

## The catalog item #1 update (sharpen what Property 2 must prove)
Catalog #1 currently reads "rmap remove side decrements more than add side when a
KAU's sub-PTEs are gapped/migrated." The hunt has REFINED this:
- An **exhaustive audit** proved every in-tree remove path (try_to_unmap_one,
  try_to_migrate_one↔remove_migration_pte, zap_present_ptes) AND every install
  path drives **clear == rmap-drop == ref-drop from one per-PTL-section count**.
  There is **no intra-function over-drop** — "remove > add per section" does NOT
  occur. Four count-based fix hypotheses A/B-refuted, consistent with this.
- A CBMC model showed an over-drop is **sufficient** for the freed-while-mapped
  end-state but is **not present** in the code's section math. So the residual bug
  is one of (being adjudicated by 4 faithful CBMC models, no injected mismatch):
  1. the **batch count itself over-counts** — `page_vma_mapped_walk`'s
     `nr_mmupages` groups sub-PTEs by `pte_pfn` only; if it ever spans two
     same-pfn mappings or the vsub≠psub file case, clear==drop but both exceed the
     one mapping → **inv2 (PTE-vector integrity)**, home `Pte.lean` + the walker;
  2. **cross-mm aggregate-free**: each mm balanced, but the section dropping the
     last *aggregate* ref frees while another mm's sub-PTEs are present, and the
     zap/exit free has no `folio_mapped()` guard → **Property 2** + the Backing
     refcount discipline (`Sharing.lean`/`Teardown.lean` category G);
  3. **outside the rmap/ref protocol**: TLB-flush coverage (**inv7/Property 1**,
     `Tlb.lean`) — weight low, QEMU probe didn't confirm; or the page-cache /
     truncate unit handling (**inv1/inv2**, the Backing + `Teardown.lean`).
**Takeaway for the proof:** Property 2 for #143 must prove the *batch-count
correctness* (`nr_mmupages` == exactly one cluster-mapping's present sub-PTEs) and
the *aggregate-free-vs-mapped gate*, NOT merely "remove ≤ add per section" (which
is already true). That is a stronger, more specific obligation than the catalog's
current framing.

## CBMC model ↔ Tessera invariant/module correspondence
| pgcl CBMC model (`rmap-ab/formal/`) | checks | Tessera invariant | Lean module |
|---|---|---|---|
| `pgcl_orphan_faithful.c` | rmap/ref/PTE protocol, no injected mismatch | inv2 + Property 2 | `Teardown`, `Fault` |
| `surf-pfnalias/` (pvmw batch over-count) | `nr_mmupages` == one mapping's sub-PTEs | **inv2** | `Pte`, walker |
| `surf-tlb/` (flush covers full cluster span) | no stale TLB ⊄ mapping | **inv7 / Property 1** | `Tlb` |
| `surf-pagecache/` (`__remove_mapping` gate, truncate units) | no page-cache-ref drop while mapped | inv1 + inv2 + Backing | `Sharing`, `Teardown` |

## What Tessera can take now
1. **Update catalog #1** with the refinement above (the over-drop is not per-section;
   it's batch-count or aggregate-free or out-of-protocol).
2. **Port a pgcl CBMC model to a Kani harness** in `rust/` where a Rust analogue
   exists (the `nr_mmupages` batch scan is the prime candidate — it's pure index
   arithmetic, ideal for Kani).
3. **Use `rmap-ab/formal/EMPIRICAL.md`** as the Property-2 threat model: the exact
   bad-state to prove unreachable (`refcount==0 && pte_present`; `mapcount<-1`),
   the assume-able preconditions (-smp1 cooperative, fork-shared file, reclaim-live),
   and the eliminations (THP/compaction/KSM/swap-excl/TLB ruled out empirically).
4. The 4 CBMC verdicts (pending) will say which surface harbors the bug or prove
   each clean — feed the survivor into the matching Lean module as the property to
   prove, and the cleared ones as discharged assumptions.

*(Authored from the pgcl CBMC/kernel shell. A copy lives at
`~/src/tessera/doc/from-pgcl-143-cbmc.md` for the Tessera shell to integrate.)*

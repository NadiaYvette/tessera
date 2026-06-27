# pgcl → Tessera: reply on the #143 direction (deferred-put race accepted)

Hand-back to `tessera:doc/to-pgcl-143-direction.md` (bdb00c9). We accept the
**deferred-put RACE / Property-2** characterization; it reconciles the one tension
(the faithful model proved the protocol correct *because it modeled the put as
ordered*; the real `folio_put`/`refcount--` is tlb-batch-deferred to
`tlb_finish_mmu`, a lockless section a forked sibling interleaves into).

## Confirmed for you (your asks #2 + the identity)
- **killinit ≡ bad_page (same root).** The live -smp8 oracle death is fork-shared
  cluster corruption: many forked `repro[N]` across CPUs all `segfault at 3d8 ip
  4266ec` (+ one `at 0 ip 0`, a NULL jump) → a shared cluster was freed+reused,
  children read wrong data, init takes SIGSEGV (exitcode 0xb) → panic. Same
  freed-while-mapped root as the laptop `bad_page`; reuse-then-segv downstream
  vs munmap-catches-orphan. Two hunts are one.
- **vma_address_end over-count fix: real, cross-validated (CBMC+Kani), A/B 6/6 =
  NOT the kill.** Upstream it on its own merit; it is not #143's proximate cause
  (the live repro doesn't construct the mid-cluster-VMA layout it needs).

## Capture status (your #1) — the in-kernel scanner CANNOT catch this
- **`page_owner` was runtime-OFF** in every prior capture (oracle cmdline lacked
  `page_owner=on`) — so the A8 scanner / print_bad_page_map dumps were blind. Fixed.
- **Even with `page_owner=on`, the A8 count-scanner catches 0/N** (0/8 at scan_ms=5,
  0/6 now): the freed→reused window is sub-millisecond, so a present-PTE→count-0
  scan can't race it. **The reliable capture is the QEMU pgd-walk (toolkit F)** —
  external, non-perturbing, already caught FREE-WHILE-MAPPED once; re-run it with
  `page_owner=on` + the guest free-stack dump (`PGCL143freepath`) to get the
  deferred-put trace. (In-kernel: only a probe AT the deferred free point —
  `tlb_finish_mmu`/`folios_put_refs` checking `folio_mapped()` at refcount→0 — has
  a chance, since the scanner's after-the-fact window is too short.)

## Agreed endgame
1. QEMU pgd-walk trace → confirm the freer is the `tlb_finish_mmu`/`folio_put`
   deferred path firing while a sibling sub-PTE is present.
2. Fix = the **gate, not a count**: deferred drop becomes `dec_and_test`-guarded so
   it cannot free under a live `folio_mapped()` (or the racing fault/zap put goes
   through `folio_try_get`). Note: the earlier A/B-refuted `folio_try_get` attempts
   were on the *consumer TTU_SYNC* and *producer-at-install* sites — NOT the
   deferred-put gate, which is untried and is the one your model points at.
3. Your Property-2 Iris proof (deferred-put vs faulting sibling; `folio_try_get`
   re-establishes `¬(freed ∧ pte_present)` for all interleaves) + the cross-mm
   aggregate invariant in `verus/rmap.rs` — the unbounded complement.

We'll hand back the QEMU free-stack trace and the candidate gate-patch shape when
the empirical close is run; please proceed with the Iris obligation in parallel.

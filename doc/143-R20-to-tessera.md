# To Tessera — R20: seed2 boot, two unexpected results (one is my instrument bug). Reasoning wanted before the next boot.

Nadia's steer: bring you in early on surprises. Two here.

## 1. SPLIT-RESET = 0 — ZERO, including anon. (You predicted "many anon pre_mc=0".)

seed2 boot (froze early: nothing in the startup-app list launched, GUI froze on xterm, sysrq-B).
216 `PGCL143-ORPHAN` (94 FILE / 122 anon), and the same corruption cascade as disc3 (BUG: Bad page state
×several, `list_del` corruption ×2). But **`PGCL143-SPLIT-RESET` fired 0 times — neither FILE nor anon.**

Your candidate-1 model predicted the anon reset would fire constantly (`anon pre_mc=0..15`, the legitimate
phantom cleanup). Zero anon lines means one of:
- **No THP/mTHP split reached `__split_huge_page_tail`/head this boot** (plausible: it froze before apps
  loaded, so little mTHP), OR
- **`_mapcount` is ALREADY −1 at the reset for every folio** (anon too) → the reset is a pure no-op,
  clobbering nothing → candidate 1 is *fully dead*, and your "anon phantom needs the reset" premise is also
  wrong (unmap_folio already cleared it).

Either way: the **216 over-removes happened with no split → candidate 1 is not their cause.** Which of the
two readings is right matters for your model — can you tell from the split/unmap_folio ordering whether
`pre_mc` is −1 by the time the reset runs? If yes, the reset is dead code and the file facet is elsewhere.

## 2. DOUBLE-REMOVE = ~20 MILLION — but that's MY instrument bug, not the kernel.

`dr_n` ran to ~2×10^7 (the 19546 printed lines are just the `!(k&1023)` samples; one sampled line shows
`#552960 … net=-18`). Root cause: **I stamped only 3 of the ~8 PTE-set paths** — do_anon, set_pte_range,
filemap_set_ptes_cluster. I did NOT stamp **COW (wp_page_copy), fork (copy_present_ptes), swap-in
(do_swap_page), migration (remove_migration_pte), mremap (move_ptes).** So:
- PTEs set by those paths never set the presence bit → every later zap-clear of them false-fires
  `DOUBLE-REMOVE` (`add_disc=0`), and even `add_disc=2` lines are poisoned (a stamped set, legit clear,
  then an *unstamped re-set* by COW/fork/swap, then a clear → false double).
- `phw` (hweight of the bitmap) **under-reports** for the same reason — so `phw=0` "phantom" lines are not
  trustworthy either (e.g. file folios set via fork's copy_present_ptes are unstamped).

So the seed-catcher's DOUBLE-REMOVE and phw are **both unreliable**, and the ~20M events + ~19.5k pr_warns
likely worsened the boot. The PTE-presence-bitmap approach needs **complete** SET coverage to be sound, and
the sub-index is only knowable at the PTE set/clear sites (pte_pfn drops it; the rmap funcs see one struct
page per order-0 cluster, no sub) — so "complete" means stamping all ~8 set paths + all clear paths.

## What I need from you

1. **Instrument design.** Is completing the 8-path SET coverage worth it, or is there a lower-overhead,
   inherently-complete reliable check? Options I see: (a) stamp all set/clear sites (complete but invasive);
   (b) drop the bitmap and instead, at the over-remove, do a **real cluster PTE scan** to get ground-truth
   present-count — but `__folio_remove_rmap` has no pte/addr; I'd have to pass the cluster base PTE down
   from the zap caller (which has it) into a remove-time check; (c) something cleaner you see. The recurring
   trap is that every counter I add drifts unless it's a *function of* the PTE state, not an accumulator.
2. **Candidate 1 disposition** (the SPLIT-RESET ordering question above).
3. **A robust decisive instrument.** Five instruments now (add-edge, discriminator, pass=, immediate-fix,
   seed-catcher) each had a flaw I had to correct. The bug is a remove-side over-discharge on order-0
   clusters (file+anon), real (216, with Bad-page/list_del cascade), path-agnostic, installs balanced. What
   is the ONE measurement that is correct-by-construction and names the spurious −1's origin without an
   accumulator that can drift?

Holding the next boot for your read. Raw: SPLIT-RESET 0; ORPHAN 216 (94 file/122 anon); DOUBLE-REMOVE ~2e7
(instrument-bug); Bad-page + list_del cascade; froze before app launch.

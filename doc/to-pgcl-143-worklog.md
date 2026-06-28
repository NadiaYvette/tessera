# #143 worklog — tessera driving (for pgcl pickup)

Running log per R21 §5. Each step: hypothesis · proof/lemma it rests on · probe/diff (vs `file:line @
f17563985f5b` or `wip/143-tier1-instruments`) · boot evidence (exact `PGCL143-*` lines) · conclusion.

## Spine (the invariant everything checks against)

`_mapcount + 1 >= present_here`, where `present_here = #{ i in [0,PAGE_MMUCOUNT) : pte_present(base[i]) ∧
pte_pfn(base[i]) == cpfn }` scanned under PTL — one-sided sound (lower bound on the true cross-mm count),
can't drift, can't false-positive. = `CallBalance` / `RemoveDual` read off the page table.
Proofs: `proof/Tessera/{CallBalance,RemoveDual,RemoveFloor,PendingGate,SingleRoot,SharingRace}.lean`.

## Bug (consolidated from R20/R21)

Remove-side over-discharge of an order-0 cluster's `_mapcount` (driven `< -1`); ~216/boot on the laptop +
`Bad page state`/`list_del` cascade. File AND anon order-0. Path-agnostic. Installs balanced. Ruled out:
install under-add (SingleRoot), deferral-as-root, THP-split reset (candidate 1, SPLIT-RESET=0), the
band-aid chain (leak-not-corrupt, not a fix).

## Env / workflow

- Drive worktree: `/home/nyc/src/linux-143-drive` (branch `drive/143-clamp` off `wip/143-tier1-instruments`),
  own objtree. Do not mutate `/home/nyc/src/linux` or `/home/nyc/src/pgcl/*`.
- On the laptop (`nyc-thinkpad`): I build + read `journalctl -k -b -1` myself; Nadia reboots + reports
  on-screen liveness (apps/pointer). Stable default = stock `6.18.13`; test kernels picked once at grub;
  `sysrq-c` on a hang → efi-pstore. /boot is a 974M partition — retire an obsolete kernel per new install.

## Step 1 — boot `-pgcl4tier1` (pending): orphan vs phantom

- **Hypothesis:** the order-0 over-removes are real orphans (cluster still mapped while `_mapcount ≤ -2`),
  i.e. `present_here > 0`. (vs phantom = `present_here == 0`, removes-to-empty-and-beyond.)
- **Probe:** pgcl's Tier-1 `PGCL143-PRESENT-HERE cpfn mc present_here anon/FILE comm` at the order-0
  over-remove, `delay_rmap=false`, seed-catcher bitmap ripped (`wip/143-tier1-instruments`).
- **Boot evidence:** _pending Nadia's boot._ Grep: `journalctl -k -b -1 | grep PGCL143-PRESENT-HERE`.
- **Decision:** `present_here > 0` dominant → Tier-2 (same invariant as `WARN_ON_ONCE` per cpfn at the
  remove sites — zap / try_to_unmap / migrate — first violation's stack = the spurious `-1`'s origin) +
  the clamp-to-`present_here` fix; `present_here == 0` dominant → remodel before touching code.
- **Boot evidence (laptop, `-pgcl4tier1+-61`, boot -1):** the staged `-61` RPM predates the present_here
  log → it emitted the *old* `PGCL143-ORPHAN` format (no `present_here`). Still decisive: **284 events,
  103 distinct clusters, each over-removed REPEATEDLY** (top capped at 15 by ratelimit; true depth `quar`
  → 42); **all `pass=1->1`** (immediate); **173 file / 111 anon**; **comm=slack** (Electron); 28-line
  `Bad page`/`list_del` cascade; partial app-launch then GUI freeze (sysrq-c → pstore).
- **Conclusion:** the R20 §4.1 **feedback loop is confirmed** — the band-aid keeps each over-removed
  cluster mappable, slack re-faults it (real present sub-PTEs), the re-zap over-removes again. A phantom
  (empty) cluster could not re-feed the loop ⇒ the over-removes are on **genuinely-mapped clusters
  (`present_here > 0`, orphan)**. Proceed straight to the clamp (Step 2), skipping a pure-observation boot.

## Step 2 — `-pgcl4clamp1`: confirm orphan + clamp-fix + name origin (BUILDING)

- **Hypothesis:** the over-discharge is a real under-count (`mc + 1 < present_here`); clamping `mc` UP to
  ground truth (`present_here - 1`, always `≥ -1`) is the correct-by-construction fix — it prevents the
  underflow (boots) and breaks the feedback (mc correct ⇒ no re-amplification).
- **Proof:** `CallBalance` (`_mapcount + 1 == Σ present`), one-sided form `mc + 1 ≥ present_here`
  (`RemoveDual`); the clamp writes ground truth into the counter.
- **Diff (`drive/143-clamp` @ worktree, `mm/memory.c` ~2050, order-0 zap remove):** replaced the log-only
  `if (mc < -1)` block with: compute `ph = pgcl143_present_here(pte, addr, pte_pfn(ptent))`; if
  `mc + 1 < ph` → `WARN_ON_ONCE(1)` (origin stack) + `PGCL143-CLAMP cpfn mc present_here … clamp->ph-1` +
  `atomic_set(_mapcount, ph - 1)`. Floor-independent (uses the invariant, not `< -1`). `delay_rmap=false`
  under PGCL so the scan sees live PTEs. Config = the booted `-pgcl4tier1+` config, `LOCALVERSION=-pgcl4clamp1`.
- **Expect:** `PGCL143-CLAMP … present_here>0` (confirms orphan + its magnitude); **boots** (clamp); each
  cluster over-discharges ONCE then is correct (no `quar` amplification); the `WARN` stack names the
  remove path. _Build in flight; boot pending Nadia._

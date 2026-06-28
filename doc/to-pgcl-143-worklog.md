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

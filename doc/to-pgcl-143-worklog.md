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
  remove path.
- **Boot evidence (laptop, `-pgcl4clamp2`… wait, `-pgcl4clamp1`, boot -1):** **ORPHAN confirmed** —
  `PGCL143-CLAMP present_here = 3,4,6,10,13` (mc+1 was 0–2 ⇒ under-counts of 3–12 on genuinely-mapped
  clusters), origin `zap_present_ptes` (mm/memory.c:2069), comm = element-desktop/openclaw/llvmpipe, all
  anon. **BUT** the clamp caught only **5** while `PGCL143-ORPHAN` reached **~9000** — my clamp sat on the
  minor `nr>1` batch path; the ~9000 flow through the `nr==1` single-zap (`zap_present_folio_ptes`) where
  the rmap floor pins `mc=-1`. **Kernel stayed ALIVE** (Nadia: clock kept updating, pointer responsive) —
  real progress over tier1's full freeze. Failure was **progressive**: a floored `mc=-1` while sub-PTEs
  present ⇒ `folio_mapped()` false ⇒ **freed-while-mapped ⇒ Bad page**; ~9000 poisoned pages accrue, tasks
  run until they draw one, GUI-management wedges last (Element/Discord/Spotify/Caprine stuck; Signal/Telegram
  ok). (sysrq L/W/T did not flush to the journal — only in pstore; the visual execution-history is the
  timeline of record here.)
- **Conclusion:** the clamp mechanism is sound but mis-sited. The corruption is **free-while-mapped driven by
  the floored mc** at the dominant `nr==1` path. Cover that path with the same clamp ⇒ mc correct ⇒
  `folio_mapped()` honest ⇒ no free-while-mapped ⇒ cascade stops.

## Step 3 — `-pgcl4clamp2`: clamp the DOMINANT path (staged, boot pending)

- **Diff (`mm/memory.c` `zap_present_folio_ptes` ~1917):** upgraded the second present_here block (the
  `nr==1` path, log-only `if (mc < -1)` — never fired, floored) to the same clamp as the batch site:
  `if (!large && mc+1 < ph) { WARN_ON_ONCE; PGCL143-CLAMP …; atomic_set(_mapcount, ph-1); }`. Now both
  zap paths clamp.
- **Boot evidence (laptop, `-pgcl4clamp2`, boot -2):** clamp engaged + broke feedback — **CLAMP 5→114
  (now 85 FILE + 29 anon), ORPHAN ~9000→125**, `present_here` mostly **14** (near-full clusters),
  comm=signal-desktop (83). **BUT Bad page persists (45)** and only Signal spawned, then unresponsive
  (gnome-shell hit a bad page). Bad-page states prove **BOTH ledgers corrupt**: `refcount:0 mapcount:1`
  (ref over-dropped → freed *while mapped*) and `refcount:1 mapcount:0` (ref leaked). pstore (clamp2
  end-sysrq): **RCU stall**, stalled CPU in `__list_add_valid_or_report` + `bad_page` under
  `rmqueue_pcplist` ⇒ **page-allocator freelist corruption** from the over-removed pages being freed in a
  bad state.
- **Conclusion (dual_lockstep, empirically confirmed):** mc-clamp is insufficient AND inflating mc without
  the ref *creates* `refcount:0 mapcount:1`. The hard5 quarantine only gates `folios_put_refs`, NOT the
  buddy/pcp free that corrupts. The boot fix must stop the over-removed page reaching the allocator on ANY
  path.

## Step 4 — `-pgcl4clamp3`: refcount PIN at the chokepoint (building)

- **Hypothesis:** the buddy only frees at refcount 0, so a real refcount pin on every over-removed folio
  covers ALL free paths → no over-removed page enters the allocator freelist → no `__list_add` corruption
  → no RCU stall → boots. Leak-not-corrupt (pin + quarantine; mc-clamp keeps the count ~125 ⇒ bounded leak).
- **Proof tie:** `Incarnation.stableref_pins` / `folio_try_get` (inc-unless-zero, never resurrects a freed
  folio — the R14 v1→v2 fix); `PendingGate`/`RemoveDual` (a held ref is leak-not-corrupt).
- **Diff (`mm/rmap.c` `pgcl143_report_orphan` ~2049, the chokepoint all over-removes pass):** after
  `pgcl143_quar_inc`, `if (!folio_try_get(folio)) pr_warn_once("PGCL143-PIN-FAIL …")`. Keeps the zap
  mc-clamps (feedback break). _Staged; boot pending Nadia._

### Step 4 result + Step 5 (root-hunt via page_owner)

- **clamp3 boot (-pgcl4clamp3, laptop):** the chokepoint pin WORKED — **Bad page 45 → 3, no OOM, RCU stall
  2** (clamp2 had many). 8 CLAMP / 89 ORPHAN / **1 PIN-FAIL** (pfn 2f9d4 "already freed at over-remove").
  The residual: that 1 PIN-FAIL is a **cross-mm deferred UAF** (folio freed by another mm *before* the
  over-remove ran → pin too late), and it is the first of the 3 Bad pages (in pmlogger) → the 2 RCU stalls
  → login wedged/failed. (Login failure ambiguous per Nadia: possible mistype, or just earlier/more-eager
  flagging — not evidence clamp3 is functionally worse; corruption is far lower.)
- **Conclusion:** the pin (refcount, all paths) handles 88/89; the 1/89 is the deferred/cross-mm UAF the
  pin can't catch post-hoc (needs a ref held *before* the free — `SharingRace.Aggregate`). But the goal is
  the zero-leak ROOT, so: don't band-aid the UAF — **name why the over-removes happen**.
- **Step 5 (no rebuild):** `CONFIG_PAGE_OWNER=y`; added `page_owner=on` to clamp3's cmdline. The ORPHAN
  handler's `dump_page` (rmap.c:2072, first 3 over-removes) will now print each over-removed cluster's
  **alloc/free/last-map incarnation history** → the pattern behind the spurious over-remove → the root op.
  Boot pending Nadia (re-test login + capture the histories).

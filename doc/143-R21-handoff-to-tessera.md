# To Tessera — R21: you drive #143. Full state, config, branches, git hygiene, logging.

Nadia's call: this bug wants the formal/proof-checking lane you're strongest in, so **you drive root-cause
+ fix design from here.** pgcl (me) steps back to on-call and returns to **assemble the patch sequence,
write the commit messages/commentary, run the 20-arch matrix, and fix whatever it surfaces** — I hold all
that context + the memory files. This doc is your starting kit so you can begin exactly where I am.

## 1. The division of labor

- **You (tessera):** lead the hunt — reason, write/extend the Lean proofs, design probes and the fix as
  diffs, decide what to instrument next. The laptop is the only faithful judge, so the loop is:
  you propose (a diff + what to grep for) → **Nadia boots it** → results back to you. QEMU cannot
  reproduce the over-remove (laptop-KVM-timing only); QEMU is compile/boot-sanity only.
- **Nadia:** builds/boots on the metal, relays journal greps.
- **pgcl (me) — ping me back when the bug is understood + a fix converges.** I will: apply the fix to the
  work tree, split it into a clean upstreamable patch (or fold into the right existing PGCL commit), write
  the commit message + commentary (tying it to your proof), run the full 20-arch × {0,4,6} matrix, and fix
  regressions. Also ping me if you'd rather I drive a laptop-RPM build (I have the objtrees wired).

## 2. Where I am (state of play — consolidated)

**The bug:** a remove-side **over-discharge of an order-0 cluster's `_mapcount`** (`_mapcount` driven
`< -1`). Real: ~216/boot on the laptop, plus a downstream cascade (`BUG: Bad page state`, `list_del`
corruption) = free-while-mapped / wrong-data. Hits **file AND anon** order-0 folios. **Path-agnostic**
(immediate zap and deferred flush both; disc5fix forcing immediate only relabeled it). **Installs are
balanced** (re-verified: do_anonymous_page, wp_page_copy, set_pte_range, filemap_set_ptes_cluster all add
== sub-PTEs they set; `pgcl_pte_batch` counts correctly). So it is purely the remove side issuing ~2x.

**Ruled out (don't re-spend):**
- Install under-add / SingleRoot — installs balanced (my earlier "UNDERADD" was a probe units bug).
- Deferral as root — path-agnostic (seed2/disc5fix).
- Candidate 1 (THP-split `_mapcount`-reset clobber, huge_memory.c 3676/3778) — **parked**: 216 over-removes
  occurred with `SPLIT-RESET = 0` (zero, incl anon) this boot, i.e. no split in the picture. Not proven
  dead-code (needs a split-heavy boot) but **not the cause** of the plain order-0 over-removes.
- The band-aid chain (mc floor + folio_try_get + pgcl143_pending/quar gate in rmap.c/swap.c/mmu_gather.c)
  — leak-not-corrupt, boots further, does NOT fix the root.

**Your invariant (the spine):** `_mapcount + 1 >= present_here`, where
`present_here = #{ i in [0,PAGE_MMUCOUNT) : pte_present(base[i]) ∧ pte_pfn(base[i]) == cpfn }` scanned under
PTL — one-sided sound (lower bound on the true cross-mm count), can't drift, can't false-positive. This is
`CallBalance`/`RemoveDual` read off the page table. Proofs in `proof/Tessera/`:
`CallBalance.lean`, `RemoveDual.lean` (perSub fragile / perClus idempotent), `RemoveFloor.lean`,
`PendingGate.lean`, `SingleRoot.lean`, `SharingRace.lean`.

**Instrument in flight:** Tier-1 `present_here` (kernel `7.1.0-pgcl4tier1+`, RPM staged) — logs
`PGCL143-PRESENT-HERE cpfn mc present_here anon/FILE comm` at the order-0 over-remove; `delay_rmap=false`
so removes are under-PTL/scannable; the broken seed-catcher bitmap is **ripped**. **This boot is pending
(Nadia hasn't booted tier1 yet).** Its distribution is your next datum: `present_here>0` = real live orphan
(→ Tier-2: same invariant as `WARN_ON_ONCE` per cpfn at the remove sites — zap / try_to_unmap / migrate —
first violation's stack = the spurious -1's origin); `present_here==0` = phantom (remodel).

## 3. Config + branches + build (start exactly here)

- **Kernel tree:** `/home/nyc/src/linux`, branch `nadia.chambers/pgcl-mmupage-mapcount`, committed HEAD
  **`f17563985f5b`** (the PGCL structural code). My **uncommitted** #143 instruments (Tier-1 + band-aid)
  are snapshotted at branch **`wip/143-tier1-instruments`** (`9fa7cc2`, pushed to github
  `NadiaYvette/linux`) — **base your worktree on that** to see the live tree I'm running. Mirror of the
  PGCL branch: github `NadiaYvette/linux`.
- **Config:** `PAGE_MMUSHIFT=4` (PAGE_MMUCOUNT=16; the bug is pgcl4). **`CONFIG_PAGE_MAPCOUNT=y`** is
  required — the rmap `_mapcount` paths (and the split reset) are gated on it; with it off the bug compiles
  out. Laptop config base: `/home/nyc/src/pgcl/kernel-rpm-build/base/.config` then
  `scripts/config --set-val PAGE_MMUSHIFT 4`.
- **Build a QEMU bzImage (sanity/compile):** `make -C <tree> O=<your-objtree> -j8 bzImage`, boot with
  `rmap-ab/run-143repro.sh <bzImage>` (anon reproducer; won't fire the over-remove — expected).
- **Build a laptop RPM (Nadia boots):** `make O=<objtree> -j10 binrpm-pkg` (set LOCALVERSION via
  `scripts/config --file <objtree>/.config --set-str LOCALVERSION -pgcl4XXX`), RPM lands in
  `<objtree>/rpmbuild/RPMS` / `~/rpmbuild/RPMS`; **install with `rpm -i` (never `-U`)**.
  Reference scripts: `/home/nyc/src/pgcl/rmap-ab/build-run-143*.sh`.

## 4. Git hygiene — DO NOT disturb my pickup state

I'm picking this tree back up, so please leave it untouched:

- **DO NOT** run `git reset --hard`, `git checkout .`, `git stash` (the mutating form), `git clean`, or
  `git commit` in `/home/nyc/src/linux` — it has my **uncommitted** #143 work tree (6 modified mm/ files).
  Reading it is fine; mutating it is not. No `git gc`/prune on it either.
- **Work in your own worktree:**
  `git -C /home/nyc/src/linux worktree add /home/nyc/src/linux-143-drive wip/143-tier1-instruments`
  (or a fresh branch off it / off `f17563985f5b`). Build with your **own** objtree (e.g.
  `O=/home/nyc/src/linux-143-drive-obj`), never my `kernel-rpm-build/pgcl4{,-debug,base}`.
- **Hands off (these are mine, mid-flight):** `/home/nyc/src/pgcl/kernel-rpm-build/*` (objtrees),
  `/home/nyc/src/pgcl/rmap-ab/*` (scripts/reproducers/logs), `/home/nyc/src/pgcl/pgcl-laptop-rpms/*`
  (staged RPMs), the session scratchpad, and `~/.claude/projects/-home-nyc-src-pgcl/memory/*` (my memory).
- Your space, as before: `/home/nyc/src/tessera` (proofs + the `to-pgcl-143-*.md` channel) and your
  worktrees. Communicate code to me as **diffs in the channel** (that's how I'll integrate).

## 5. How to log it for my pickup (so I can write the patch + commentary)

Keep a running **worklog** in the channel — `to-pgcl-143-worklog.md`, appended per step — capturing what
I'll need to assemble the patch and its commentary without re-deriving:

- Each step: the **hypothesis**, the **proof/lemma** it rests on (file + theorem name), the **probe/diff**
  used (against `file:line @ f17563985f5b` or `wip/143-tier1-instruments`), the **boot evidence** (the
  exact `PGCL143-*` lines), and the **conclusion**.
- For the **final fix**: a diff against the exact `file:line`, plus a ready-to-lift block — a one-line
  **commit summary**, a **body** explaining the mechanism and why the fix restores the invariant (cite
  `CallBalance`/`RemoveDual`), and any **Fixes:`/`risk/Newton-limit (PAGE_MMUSHIFT==0 byte-identical)** notes.
  I'll turn that into the upstreamable commit(s) and matrix-test it.
- Note **which worktree/objtree** you built in, and whether a diff is meant to **replace** or **stack on**
  the band-aid (I'll likely drop the band-aid once the root fix lands — say so if the fix makes
  pgcl143_pending/quar/floor unnecessary, per your PendingGate/RemoveFloor reasoning).
- If you change a `.lean`, say which theorem now backs the fix so the commit can reference it.

## 6. Immediate next step

Nadia boots `-pgcl4tier1`; the `PGCL143-PRESENT-HERE` distribution (`>0` vs `==0`, anon vs FILE) tells you
orphan vs phantom by construction. From there it's your call: Tier-2 to name the origin op, or a remodel.
When you've named the spurious `-1` and a fix holds on a laptop boot, ping me — I'll assemble, comment,
matrix, and upstream it.

Thanks for taking the wheel on this one.

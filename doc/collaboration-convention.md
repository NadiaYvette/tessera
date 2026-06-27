# Multi-repo / multi-shell collaboration convention

How the Tessera verification effort and the implementation projects (telix, pgcl)
cooperate across separate repositories and separate Claude shells — written so a new
shell, or a developer who inherits this later, can pick it up without the original
context.

## The shape of the effort

Three repositories, each typically driven by its own Claude shell, on one machine
(shared filesystem) and pushed to the same four mirrors (github, sourcehut, disroot,
framagit):

| Repo | Role | Tools |
|---|---|---|
| **tessera** (`~/src/tessera`) | **Spec authority.** Proves *what correct means* for the clustered-superpage VM — the invariants, the refinement tower, and a **bug catalogue** mined from telix+pgcl. Drafts and verifies specs; renders invariants as checkable properties. | Lean 4 (∀N, abstract), Kani (bounded, Rust), Verus (in-tree, drafts) |
| **telix** (`~/src/telix`) | **Rust implementation + in-tree Verus.** Owns the `#![no_std]` build, the real data structures, CI. Integrates verified specs into mainline `mm/`. | Verus in its build system |
| **pgcl** (`~/src/pgcl`, `~/src/linux-pgcl-mc`) | **Linux C implementation + CBMC bughunting.** Hunts real bugs in the deployed C with bounded model checking, bridged to Tessera's invariants. | CBMC (C) |

**Key kinship:** Kani (Tessera's Rust harnesses) *is* CBMC. So a pgcl CBMC model and a
Tessera Kani harness are the same engine on the two languages; Tessera's Lean theorems
are the unbounded (∀N) complement to both bounded checks.

## The collaboration mechanisms (no direct shell-to-shell IPC)

The shells do **not** message each other directly. They cooperate through three channels:

1. **Git branches as shared workspaces.** Work destined for another repo goes on a
   **dedicated branch in that repo** (e.g. `verus-extent` in telix). Both shells read/write
   it; it's pushed to the four mirrors so it's durable. One shell drafts, the other
   integrates, both trade commits through the branch.
2. **Hand-off documents** are explicit, committed artifacts so the relay is lossless:
   - telix-side: `telix:verus/{README,CORRESPONDENCE,TOOLCHAIN}.md` — the plan, the
     clause-by-clause `Verus⟷Kani⟷Lean` map, the toolchain/version strategy.
   - pgcl-side: `pgcl:rmap-ab/formal/{TESSERA-BRIDGE,EMPIRICAL}.md` — the CBMC findings
     and the `CBMC⟷Tessera` correspondence; a copy lands in
     `tessera:doc/from-pgcl-143-cbmc.md` for the Tessera shell to integrate.
   - tessera-side: `doc/failure-modes-*.md` (the catalogue), `doc/proof-obligations.md`.
3. **The human orchestrator** relays intent ("pgcl produced X; tessera, reciprocate").
   The hand-off docs exist precisely so this relay carries no hidden state.

## Worktree convention (do not disturb another shell's checkout)

When one shell must work on a branch in a repo another shell is actively using, use a
**git worktree** — never switch the shared checkout:

```sh
git -C ~/src/telix worktree add ~/src/telix-verus -b verus-extent master
# ...work in ~/src/telix-verus on verus-extent; the main ~/src/telix checkout is untouched...
```

A branch checked out in a worktree can't also be checked out in the main tree; the other
shell fetches the *pushed* branch and adds its own worktree. Remove a worktree with
`git worktree remove` when done (the branch persists).

## Conventions

- **Branch names** describe the work (`verus-extent`); push to the `all` mirror remote:
  `GIT_SSH_COMMAND='ssh -o BatchMode=yes' git push all <branch>`.
- **Commit trailers** (every commit): `Co-Authored-By: Claude Opus 4.8 …` and a
  `Claude-Session:` line. Copy the exact format from `git log -1`.
- **Cross-validation, not duplication.** The same invariant is proved by more than one
  tool on purpose (Lean = it's the right invariant ∀N; Kani/CBMC = this code meets it,
  bounded; Verus = it meets it in-tree, in CI). Always read the other repo's findings
  before re-deriving — the bug catalogue and the bridge docs say what's already known.
- **Reproducibility scripts** live with the proofs: `telix:verus/verify.sh` (Verus),
  `tessera:rust/*/` (`cargo kani`), `tessera:proof/` (`lake build`),
  `pgcl:rmap-ab/formal/*/run.sh` (CBMC).
- **Version coordination** (Verus ⟷ Rust): see `telix:verus/TOOLCHAIN.md`. A Verus bump
  is a coordinated step — tessera green-lights the specs (re-runs `verify.sh`), telix
  green-lights the build/CI.

## Picking this up cold (for a later developer)

1. Start at `tessera:doc/RESULTS.md` (what's proved) and `doc/proof-obligations.md` (the map).
2. The catalogue (`doc/failure-modes-*.md`) is the threat model — *every* theorem targets
   a real telix/pgcl bug; it is also the shared property list driving telix's Verus and
   pgcl's CBMC.
3. Per subsystem, the chain is: Lean theorem (`proof/Tessera/*.lean`) → Kani harness
   (`rust/*/`) → in-tree Verus (`telix:verus/`) / CBMC (`pgcl:rmap-ab/formal/`). The
   `CORRESPONDENCE.md` / bridge docs link the layers.
4. To extend: draft + verify the spec in tessera (the authority), then hand it to the
   owning implementation repo via a branch + a correspondence entry.

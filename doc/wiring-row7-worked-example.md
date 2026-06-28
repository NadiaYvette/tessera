# Wiring a catalogue row, end-to-end — the worked example (row #7, the LLFree allocator)

The deferred-maintenance catalogue lists eight deferral sites, each against one obligation. A row in
the OPEN state is *only a spec* — nothing is connected to the running kernel. **"Wiring" a row** turns
that spec into a check that *fails when the code is wrong*. This is row #7 done end-to-end, as the
template for rows #4–#8.

Row #7 is the **LLFree per-CPU physical allocator** (telix `kernel/src/mm/phys.rs`). It is a family-(A)
site: a reserved chunk's pages may be reused, and the guard that must hold is *"the reservation pins
the chunk exclusively."* What makes it the ideal first worked example is that **telix already ships the
runtime half** — the `DI_SHADOW` detector — and it turns out to be *literally* the framework's
incarnation probe. So wiring this row is mostly recognizing what is already there and proving it sound.

The three steps:

## Step 1 — INSTANCE (≈1 line): map the allocator onto the framework

Read the site and name the four roles. For the allocator:

| framework role | the allocator's reality (telix `mm/phys.rs`) |
|---|---|
| resource `R` | a physical page |
| guard (`Deferred.Pinned`, family A) | the per-CPU **chunk reservation** — `ChunkNode.owner_cpu` [13:7], `0x7F` = unowned. While CPU `a` owns a chunk, only `a` allocs its pages. |
| incarnation (`Incarnation.Pfn`) | a page's **allocation** — handed to an owner. free+realloc = the next incarnation. |
| the bug (`reincarnate_breaks`) | a page handed out **while still owned** = the #228 "PA-ALIAS" double-issue. |
| the runtime probe (`Incarnation.probeFires`) | **`DI_SHADOW`**: `di_shadow_alloc` does `fetch_or` and fires if the bit was already set. |

That last row is the payoff: `di_shadow_alloc`'s "`fetch_or` finds the bit already set" is, character for
character, `probeFires` — *"a deferred/aliased op targets a frame whose incarnation has moved."* The
probe we proved faithful in the abstract is the detector telix wrote by hand for a different bug.

## Step 2 — AUDIT: state the obligation, hunt the gap, read the result

**Obligation.** A page's shadow bit is set by exactly one owner at a time; `alloc` must `fetch_or` a
*clear* bit (the page was free). A `fetch_or` that finds it *set* is a page issued while still owned.

**Gap to hunt.** A reservation that is *not* exclusive — a chunk owned by two CPUs — would let both
alloc the same page. That is the concrete shape of the family-(A) failure for this site.

**Result (read off the running kernel).** pgcl/telix ran `DI_SHADOW` under stress and **it never
tripped.** By `Incarnation.pinned_silences_probe` (probe silent ⟺ the guard discharges the obligation),
that is not "we didn't look hard enough" — it is *the obligation is met*: the reservation pins
exclusively, and the #228 corruption is **not** a page double-issue. The audit's job is exactly this —
turn a runtime observation into a discharged (or violated) obligation. Here it discharges, and it sends
the #228 hunt elsewhere (the corruption is upstream of the allocator), which is itself a result.

## Step 3 — CHECK: make a regression *fail*, two ways

Wiring means both halves, so a future change that breaks the obligation is caught statically *or* at
runtime:

- **Static (in-tree Verus)** — `telix-verus:verus/phys_reservation.rs` (✅ `3 verified, 0 errors`), the
  allocator twin of `phys_chunk.rs`:
  - `double_alloc_fires` — once a page is allocated, a second alloc of it *fires the probe*; the
    allocator cannot hand it out twice unseen. (The #228 obligation, on the global shadow.)
  - `free_then_alloc_silent` — after a correct `free` (release), re-issuing the page does *not* fire:
    the legitimate reincarnation, distinguished from the claim-while-owned bug.
  - `reservation_exclusive` — a chunk has at most one owner, so two CPUs never both alloc its pages.
    This is the family-(A) `Pinned` for the allocator; a code change that let two CPUs co-own a chunk
    would fail this proof in CI.
- **Runtime (the probe)** — `DI_SHADOW` *is* the incarnation probe; it is already in the tree behind a
  `const` flag (off by default, no per-alloc cost; flip on to re-verify). As an A/B instrument it is
  faithful: a candidate change that reintroduces double-issue drives it `>0`, and only a change that
  truly restores exclusivity drives it back to `0/N`.

## The shape, transferable to rows #4–#8

The row went `OPEN spec → GREEN checked` without a new reproducer, and the static + runtime checks now
stand guard. The recurring moves:

1. **Name the four roles** (resource / guard / incarnation / probe) — one table.
2. **State the obligation and the gap** in the guard's terms; **read the runtime result** as a
   discharge-or-violation via `pinned_live` / `pinned_silences_probe`.
3. **Write the in-tree check** (a small Verus twin proving the guard), and **identify-or-add the runtime
   probe** (often a `fetch_or`/refcount assert already present, as here).

For the remaining rows the probe usually is *not* already in the tree — #4 (RCU grace pins the node),
#5 (collapse holds folio refs), #8 (writeback ref until IO completes) — so step 3 adds it. But the
instance + audit are the same one-table, one-obligation move, and `Deferred.Window` / `Incarnation`
hand you the soundness for free.

---

## Applying the template — row #6 (migration ref-pin), in brief

The second row, to show the moves transfer. Migration finishing (`mm/migrate.c`) carries two
obligations; the *placement* half (each sub-PTE restored to the right psub) was already proved latent
in `Permute`/`MigrateEntry`, so only the *ref-pin* half needed wiring (`proof/Tessera/MigrationPin.lean`,
axiom-clean).

**1. INSTANCE — the four roles:**

| framework role | migration's reality |
|---|---|
| resource `R` | the source folio being migrated |
| guard (`Pinned`) | the migrator's refs, held at *exactly* `expected_count = mapped + 1` (the `+1` = its isolation ref) |
| incarnation | the source folio's allocation; it must not be freed+reused before `remove_migration_ptes` |
| the probe / guard-enforcer | **`folio_ref_freeze(expected_count)`** — atomically asserts `refcount == expected`, else `-EAGAIN` |

**2. AUDIT.** Obligation: the migrator may swap the mapping only while it holds every reference itself
(none stray). `folio_ref_freeze` enforces it atomically: equal → freeze and proceed; unequal → back
off. The gap to hunt would be a mapping swap *not* behind the freeze — there is none. Result: the
obligation is discharged *in-tree, already* (`frozen_pinned`, `frozen_live`, `stray_ref_aborts`).

**3. CHECK.** Static: `MigrationPin.lean` proves the freeze discharges `Pinned` (`frozen_pinned`) and
incarnation-correctness (`frozen_inc_correct`), and that a stray ref aborts (`stray_ref_aborts`).
Runtime: the freeze *is* the enforcer — a mismatch is already an `-EAGAIN`, no probe to add.

**The payoff.** `freeze_implies_tryget` proves a successful freeze implies `refs > 0` — so migration's
guard is the **exact-count (`==`) form of #143's try-get (`> 0`)**, the same `Pinned` family in its
strictest grade. This is why row #6's ref-pin was *already correct* while row #2's was the live laptop
bug: the kernel **froze** migration but only `_get`-ed (not `try_get`-ed) the zapped cluster. The
framework places both under one obligation and shows precisely which grade each site uses — and which
site was missing it.

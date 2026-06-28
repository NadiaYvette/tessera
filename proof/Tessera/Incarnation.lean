/-
  Tessera — INCARNATION-CORRECTNESS: the freed-then-reused (ABA) refinement of deferred-maintenance
  safety (pgcl #143 R12).

  R12 refuted R11's `delay_rmap=false` fix on the REAL laptop: gating the deferred-rmap path just moved
  the over-remove to the immediate free path (`tlb_finish_mmu -> folios_put_refs`, 186 bad_page). The
  over-remove is PATH-INDEPENDENT. The sharper mechanism: a teardown op (rmap removal OR ref drop)
  OUTLIVES the cluster's free and lands on the NEXT INCARNATION of the same pfn (`free_ts < alloc_ts`;
  reused by `wp_page_copy`) -> `mapcount -1`. So the obligation is not about one deferred *window* but
  about the FRAME: a teardown op must target the folio *incarnation* the sub-PTE was installed against,
  never a later reuse — INCARNATION-CORRECTNESS.

  This refines `Deferred.lean`: there the guard kept "a refcount" positive; here we make the ABA
  explicit (a pfn freed and re-allocated to a new owner, a new incarnation) and show the Deferred
  obligation — a stable existence ref — is exactly what blocks the reincarnation, PATH-INDEPENDENTLY.
  We model the three fixes pgcl named and state which discharges the obligation most cleanly (the
  spec-authority call) in `doc/to-pgcl-143-convergence.md` §11.

  Methodological (R12): the smp8 oracle is UNFAITHFUL (clean there, regression on the laptop), so
  empirical A/B mis-steered. Formal reasoning needs no reproducer — it ranges over all interleavings —
  which is why this obligation, not another oracle round, is the path to the fix.
-/
import Tessera.Deferred

namespace Tessera
namespace Deferred

/-- A physical frame (`pfn`) across reincarnations: `inc` = the current incarnation (epoch, bumped on
each free+realloc), `refs`/`mapc` = the CURRENT incarnation's reference and rmap counts. A teardown op
was scheduled against some incarnation `e` (the sub-PTE was installed when the frame was incarnation
`e`). -/
structure Pfn where
  inc  : Nat
  refs : Int
  mapc : Int
deriving Repr

/-- free + realloc: the frame's refs reached 0 and it is handed to a NEW owner — incarnation `inc+1`
with fresh counts. -/
def Pfn.reincarnate (p : Pfn) (newRefs newMapc : Int) : Pfn :=
  { inc := p.inc + 1, refs := newRefs, mapc := newMapc }

/-- A deferred rmap removal decrements the current frame's mapcount. -/
def Pfn.rmapRemove (p : Pfn) : Pfn := { p with mapc := p.mapc - 1 }

/-- **Incarnation-correct**: the op scheduled for incarnation `e` finds the frame still at `e`. -/
def IncCorrect (p : Pfn) (e : Nat) : Prop := p.inc = e

/-- **THE R12 BUG — a stale teardown op on a reincarnated frame.** After free+realloc the incarnation
has advanced, so an op scheduled for the OLD incarnation `e` is no longer correct. -/
theorem reincarnate_breaks (p : Pfn) (e : Nat) (he : p.inc = e) (nr nm : Int) :
    ¬ IncCorrect (p.reincarnate nr nm) e := by
  simp only [IncCorrect, Pfn.reincarnate]; omega

/-- …and the stale removal CORRUPTS the new incarnation: it drives the freshly-allocated incarnation's
mapcount one below its true value — exactly the laptop's `mapcount -1` when the new incarnation is a
just-allocated, unmapped page (`mapc = 0`). -/
theorem stale_remove_corrupts (p : Pfn) (nr nm : Int) :
    ((p.reincarnate nr nm).rmapRemove).mapc = nm - 1 := by
  simp only [Pfn.reincarnate, Pfn.rmapRemove]

theorem stale_remove_underflows (p : Pfn) (nr : Int) :
    ((p.reincarnate nr 0).rmapRemove).mapc = -1 := by
  simp only [Pfn.reincarnate, Pfn.rmapRemove]; omega

/-- free+realloc is only possible once the current incarnation is fully released (`refs ≤ 0`). -/
def CanReincarnate (p : Pfn) : Prop := p.refs ≤ 0

/-- **FIX (a) — stable existence ref / `folio_try_get` (the recommended, path-independent).** While a
teardown holds a *real* stable ref keeping `refs > 0`, the frame CANNOT be freed+reused, so its
incarnation cannot change. One ref pins the frame for EVERY in-flight teardown op (rmap removal AND ref
drop), whatever path each takes — which is why this dissolves R12's path-independence. -/
theorem stableref_pins (p : Pfn) (hlive : 0 < p.refs) : ¬ CanReincarnate p := by
  simp only [CanReincarnate]; omega

theorem stableref_inc_correct (p : Pfn) (e : Nat) (he : p.inc = e) (hlive : 0 < p.refs) :
    IncCorrect p e ∧ ¬ CanReincarnate p :=
  ⟨he, stableref_pins p hlive⟩

/-- **The Deferred obligation IMPLIES incarnation-correctness** — the two layers compose. A `Pinned`
deferred op (`Deferred.pinned_live`) keeps `refs > 0`, which blocks reincarnation. So R12's
path-independence is *why* the obligation belongs on the FRAME (`refs`), not on any one deferred path:
`Pinned` already pins the incarnation. -/
theorem pinned_inc_correct (w : Window) (p : Pfn) (e : Nat)
    (hw : p.refs = w.refs) (he : p.inc = e) (hp : w.Pinned) (ho : 0 < w.owed) :
    IncCorrect p e ∧ ¬ CanReincarnate p := by
  have hl := pinned_live w hp ho
  simp only [Window.live] at hl
  exact ⟨he, by simp only [CanReincarnate]; omega⟩

/-- **FIX (c) — incarnation tag.** The deferred op carries its target `e` and checks the current
incarnation before acting; on a reuse mismatch it is a no-op. Robust but invasive (tag + check at
every teardown decrement). -/
def Pfn.taggedRemove (p : Pfn) (e : Nat) : Pfn :=
  if p.inc = e then { p with mapc := p.mapc - 1 } else p

/-- A tagged removal never corrupts a reincarnated frame: on mismatch it leaves it untouched. -/
theorem taggedRemove_safe_on_reuse (p : Pfn) (e : Nat) (hne : p.inc ≠ e) :
    p.taggedRemove e = p := by
  simp only [Pfn.taggedRemove, if_neg hne]

/-- **FIX (b) — ordering** (clear + rmap-drop + ref-drop as one ordered unit, the freeing drop LAST):
every op of incarnation `e` runs before any reincarnation, so it is trivially incarnation-correct. A
consequence of (a): a held ref makes the free (gated on `refs ≤ 0`) the last step. -/
theorem ordered_inc_correct (p : Pfn) (e : Nat) (he : p.inc = e) : IncCorrect p e := he

/-! ## The incarnation PROBE — a FAITHFUL A/B instrument (runtime wiring of catalogue row #2)

The fix-(c) check `inc == e`, used as a *detector* rather than a fix. Unlike a symptom catcher
(`PGCL143-RMTRIP` fires only once mapcount already went negative — reactive, and *silenced* by a fix
that merely moves the catch-site, e.g. `delay_rmap=false`), the incarnation probe fires AT THE CREATOR:
the instant a deferred op targets a reincarnated frame, path-independently. So it is the faithful A/B
signal the smp8 oracle was not — and it is exactly the runtime form of `pinned_inc_correct`. -/

/-- The probe at a deferred op scheduled for incarnation `e`: does the current frame mismatch? -/
def probeFires (p : Pfn) (e : Nat) : Bool := decide (p.inc ≠ e)

/-- **The probe is exact**: it fires iff the op is incarnation-INCORRECT — no false positives, no
false negatives. -/
theorem probe_faithful (p : Pfn) (e : Nat) : probeFires p e = true ↔ ¬ IncCorrect p e := by
  simp only [probeFires, IncCorrect, decide_eq_true_eq, ne_eq]

/-- **A reincarnation FIRES the probe** — the bug is caught at its creator, not its symptom. -/
theorem reincarnate_fires_probe (p : Pfn) (e : Nat) (he : p.inc = e) (nr nm : Int) :
    probeFires (p.reincarnate nr nm) e = true := by
  simp only [probeFires, Pfn.reincarnate, decide_eq_true_eq, ne_eq]; omega

/-- **A correctly-fixed (stable-ref-pinned) teardown SILENCES the probe** and keeps it silent (the
frame cannot reincarnate). So `probe → 0/N` is *exactly* the A/B signal that a candidate fix discharges
the obligation — and a fix that only relocates the over-remove (R12's `delay_rmap=false`) still fires
it, which is why this probe does not lie the way the oracle did. -/
theorem pinned_silences_probe (p : Pfn) (e : Nat) (he : p.inc = e) (hlive : 0 < p.refs) :
    probeFires p e = false ∧ ¬ CanReincarnate p := by
  refine ⟨?_, stableref_pins p hlive⟩
  simp [probeFires, he]

end Deferred
end Tessera

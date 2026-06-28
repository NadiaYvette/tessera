/-
  Tessera — MIGRATION REF-PIN: wiring deferred-maintenance catalogue ROW #6, the ref-pin half.

  Row #6 (page migration finishing) carries TWO obligations. The *placement* half — that
  `remove_migration_ptes` restores each sub-PTE to the correct psub — is already proved latent in
  `Permute.lean` / `MigrateEntry.lean`. This file wires the *ref-pin* half: the source folio must stay
  live (and its incarnation fixed) across the whole isolate → copy → `remove_migration_ptes` window,
  so the deferred restoration never lands on a freed or reused folio.

  The mechanism in `mm/migrate.c` (`__folio_migrate_mapping`): the migrator holds
  `expected_count = folio_expected_ref_count(folio) + 1` references (the `+1` is its isolation ref) and
  swaps the mapping only behind `folio_ref_freeze(folio, expected_count)` — an ATOMIC check that the
  refcount is EXACTLY `expected` (no stray reference is racing) which then pins it for the swap; a
  mismatch returns `-EAGAIN`. That exact-count freeze is migration's form of #143's fix-(a) try-get:
  proceed only if the refs are what I require, else back off. We show it discharges the same `Pinned`
  obligation (`Deferred.lean`) and the same incarnation-correctness (`Incarnation.lean`).
-/
import Tessera.Deferred
import Tessera.Incarnation

namespace Tessera
namespace Deferred

/-- Migration's ref-pin state. `refs` = the source folio's current refcount; `mapped` = the references
the migration will restore to the new folio (the owed maintenance — `remove_migration_ptes`). -/
structure Migration where
  refs   : Int
  mapped : Nat
deriving Repr

/-- `expected_count`: the mapped references plus the migrator's own isolation ref (`+1`). -/
def Migration.expected (m : Migration) : Int := (m.mapped : Int) + 1

/-- `folio_ref_freeze(expected)` succeeds iff the refcount is EXACTLY `expected` — i.e. no stray
reference is racing the migration. -/
def Migration.freezeSucceeds (m : Migration) : Prop := m.refs = m.expected

/-- The migration as a deferred-maintenance `Window`: the guard is the held refs, the owed maintenance
is the mapped references `remove_migration_ptes` must restore. -/
def Migration.toWindow (m : Migration) : Window := { refs := m.refs, owed := m.mapped }

/-- **The freeze discharges `Pinned`.** A successful freeze (`refs = mapped + 1`) makes every owed unit
backed by a real ref, with the isolation ref as the strict surplus — the family-(A) obligation for
migration, met. -/
theorem frozen_pinned (m : Migration) (hf : m.freezeSucceeds) : m.toWindow.Pinned := by
  simp only [Migration.freezeSucceeds, Migration.expected] at hf
  simp only [Window.Pinned, Migration.toWindow]
  omega

/-- …so the source folio is LIVE across the whole window — it cannot be freed while migration entries
still owe restoration (`pinned_live`). The migration twin of #143's deferred-teardown obligation. -/
theorem frozen_live (m : Migration) (hf : m.freezeSucceeds) (ho : 0 < m.mapped) :
    m.toWindow.live :=
  pinned_live m.toWindow (frozen_pinned m hf) (by simp only [Migration.toWindow]; omega)

/-- **A stray reference ABORTS the migration** (`-EAGAIN`): if another holder has a reference the
migrator did not account for (`expected < refs`), the freeze FAILS, so the migrator never swaps the
mapping of a folio another actor might free or reuse. The guard refuses rather than races — the
discipline `unpinned_freed_while_owed` says is mandatory, enforced atomically. -/
theorem stray_ref_aborts (m : Migration) (hstray : m.expected < m.refs) : ¬ m.freezeSucceeds := by
  simp only [Migration.freezeSucceeds]; omega

/-- **The freeze prevents reincarnation across the window.** With the isolation ref counted in
`expected`, a successful freeze keeps `refs > 0`, so the source folio cannot be freed+reused while the
deferred `remove_migration_ptes` is still owed — incarnation-correctness, the very `pinned_inc_correct`
guard #143 R12 needed. So migration already does, exactly, what the zap teardown must learn to do. -/
theorem frozen_inc_correct (m : Migration) (p : Pfn) (e : Nat)
    (hf : m.freezeSucceeds) (ho : 0 < m.mapped)
    (hpr : p.refs = m.toWindow.refs) (he : p.inc = e) :
    IncCorrect p e ∧ ¬ CanReincarnate p :=
  pinned_inc_correct m.toWindow p e hpr he (frozen_pinned m hf)
    (by simp only [Migration.toWindow]; omega)

/-- **Migration's freeze subsumes #143's try-get.** A successful exact-count freeze implies `refs > 0`
(the try-get condition), so the migration guard is at least as strong as the zap-teardown guard — the
same `Pinned` family, in its strictest (equality) form. This is why row #6's ref-pin is *already*
discharged in-tree while row #2's was the live bug: the kernel froze migration but only `_get`-ed,
not `try_get`-ed, the zapped cluster. -/
theorem freeze_implies_tryget (m : Migration) (hf : m.freezeSucceeds) : 0 < m.refs := by
  simp only [Migration.freezeSucceeds, Migration.expected] at hf; omega

end Deferred
end Tessera

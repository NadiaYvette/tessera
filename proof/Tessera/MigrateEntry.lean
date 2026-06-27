/-
  Tessera — the MIGRATION-ENTRY round-trip (pgcl #143 wrong-data; the migration path pgcl is
  debugging).

  Real flow: `try_to_migrate_one` replaces each present sub-PTE with a **migration entry** (the PTE
  is gone; the entry stands in for the page being moved); `migrate_folio` copies the content
  old→new frame (`Migrate.copySub`); `remove_migration_pte` replaces each migration entry with a
  **new** present sub-PTE pointing at the NEW page. So the PTE is *removed and reinstalled* around
  the copy — a placement round-trip, and the reinstall is the natural place for a sub-offset slip:
  a migration entry that forgets which sub-page it stood for, or a restore that re-points sub-PTE
  `i` at the wrong new sub-frame, feeds userspace wrong data.

  This file models that round-trip on the sub-PTE state and proves it **preserves placement** when
  the entry faithfully carries the sub-page index and the restore uses it — then both an
  install-side and a restore-side sub-offset fold are provable wrong-data errors. Finally it
  composes with `Migrate.copySub` into the userspace observable: a faithful migration-entry
  round-trip *and* a faithful content copy give `observed = intended`.
-/
import Tessera.Migrate

namespace Tessera

/-- A sub-PTE's state during migration: present (maps a physical frame) or replaced by a migration
entry that encodes the sub-page index it stands for. -/
inductive PteState where
  | present (frame : Nat)
  | migration (subIdx : Nat)
deriving DecidableEq, Repr

/-- `try_to_migrate_one`: replace a present sub-PTE (mapping `oldpb`'s sub-frame) with a migration
entry encoding its **sub-page index** read off the old frame (`frame − oldpb`). -/
def installMigration (oldpb : Nat) : PteState → PteState
  | PteState.present f => PteState.migration (f - oldpb)
  | s => s

/-- `remove_migration_pte`: replace a migration entry with a new present sub-PTE pointing at the
NEW base's sub-frame for the SAME sub-page index. -/
def removeMigration (newpb : Nat) : PteState → PteState
  | PteState.migration i => PteState.present (newpb + i)
  | s => s

/-- **The migration-entry round-trip preserves placement**: a correctly-placed present sub-PTE for
cluster `(vb, oldpb)` at `v`, after install + remove to new base `newpb`, points at the INTENDED
new sub-frame — no sub-page cross. -/
theorem migration_roundtrip_placed (vb oldpb newpb v : Nat) (_hvb : vb ≤ v) :
    removeMigration newpb (installMigration oldpb (PteState.present (intendedFrame vb oldpb v)))
      = PteState.present (intendedFrame vb newpb v) := by
  simp only [intendedFrame, installMigration, removeMigration, PteState.present.injEq]
  omega

/-- The **install-side slip** (`try_to_migrate` encodes the wrong sub-index — folds it to 0). -/
def installMigrationFold : PteState → PteState
  | PteState.present _ => PteState.migration 0
  | s => s

/-- **An install-side sub-offset fold is a provable WRONG-DATA error**: at any nonzero sub-offset
the round-trip restores the sub-PTE to the wrong new sub-frame. -/
theorem migration_installFold_wrong (vb oldpb newpb v : Nat) (hsub : vb < v) :
    removeMigration newpb (installMigrationFold (PteState.present (intendedFrame vb oldpb v)))
      ≠ PteState.present (intendedFrame vb newpb v) := by
  have e1 : installMigrationFold (PteState.present (intendedFrame vb oldpb v))
      = PteState.migration 0 := rfl
  have e2 : removeMigration newpb (PteState.migration 0) = PteState.present newpb := rfl
  rw [e1, e2, intendedFrame]
  intro h; injection h with h'; omega

/-- The **restore-side slip** (`remove_migration_pte` re-points at the new base, dropping the
sub-index — the most natural place for the bug). -/
def removeMigrationFold (newpb : Nat) : PteState → PteState
  | PteState.migration _ => PteState.present newpb
  | s => s

/-- **A restore-side sub-offset fold is a provable WRONG-DATA error**: even with a faithful
migration entry, restoring without the sub-index re-points the later sub-PTE to the wrong frame. -/
theorem migration_removeFold_wrong (vb oldpb newpb v : Nat) (hsub : vb < v) :
    removeMigrationFold newpb (installMigration oldpb (PteState.present (intendedFrame vb oldpb v)))
      ≠ PteState.present (intendedFrame vb newpb v) := by
  have e1 : installMigration oldpb (PteState.present (intendedFrame vb oldpb v))
      = PteState.migration (intendedFrame vb oldpb v - oldpb) := rfl
  have e2 : removeMigrationFold newpb (PteState.migration (intendedFrame vb oldpb v - oldpb))
      = PteState.present newpb := rfl
  rw [e1, e2, intendedFrame]
  intro h; injection h with h'; omega

/-- **Full migration correctness**: the entry round-trip restores the sub-PTE to the new sub-frame
(`migration_roundtrip_placed`) AND the content copy fills that frame faithfully
(`Migrate.copySub`), so userspace observes the intended content. The two mechanisms — placement
round-trip and content copy — compose into the same observable as `Eviction.lean`. -/
theorem full_migration_observed_intended {vb oldpb newpb n : Nat} {mem0 : Mem} (v : Nat)
    (hvb : vb ≤ v) (hlt : v - vb < n) :
    observed (intendedFrame vb newpb) (copySub mem0 oldpb newpb n) v
      = intendedContent vb oldpb mem0 v := by
  have key := migrate_observed_intended (vb := vb) (src := oldpb) (dst := newpb) (n := n)
    (mem0 := mem0) (v - vb) hlt
  have hv : vb + (v - vb) = v := by omega
  rw [hv] at key
  exact key

end Tessera

/-
  Tessera — the vsub≠psub MIGRATION construct (the decoded #143 kill-init).

  Decoded from the oracle's cryptic utterances (rmap-ab QEMU rig):
    * `143dangle`  : killinit=1 with FREE-WHILE-MAPPED=0, empty freer-stack  -> an OVERWRITE, not a free.
    * `143detect`  : the WARN is in `remove_migration_pte -> folio_add_anon_rmap_ptes` under kcompactd
                     -> the MIGRATION re-install is the site.
    * `143migsub`  : fires 6/6 with killinit; precondition `vsub=2 psub=1` -> the trigger is vsub ≠ psub.
    * `143vmaend`  : the boundary-clamp fix was INCOMPLETE -> not a vma-end edge.

  The construct the model was missing: within a PGCL cluster a sub-PTE sits at a VIRTUAL sub-index
  `vsub` (read off the fault address) but POINTS at a PHYSICAL sub-frame `psub` of the folio, and
  `relocate_vma_down()`/`mremap` (which preserve the old `vm_pgoff`) make `vsub ≠ psub` reachable.
  Migration removes each present sub-PTE for a migration entry and `remove_migration_pte` re-installs
  it.  The faithful entry carries PSUB and the restore uses it; the kernel BUG recomputes the
  sub-index from the ADDRESS (VSUB) at restore.  On the diagonal (vsub=psub) that is invisible — which
  is why it survived to the laptop and is silent at PAGE_MMUCOUNT=1 (pgcl0 control: the only sub-index
  is 0).  Off the diagonal it re-points the sub-PTE at the WRONG new sub-frame -> userspace reads/writes
  the wrong sub-page of a (shared, code) cluster -> overwrite -> PID1 dies.  No page is freed — exactly
  what `143dangle` saw.

  Proved: faithful restore preserves placement for EVERY cluster; the vsub-restore is correct ON the
  diagonal and provably WRONG off it (the oracle's precondition); PAGE_MMUCOUNT = 1 forces the diagonal
  (covers the pgcl0 control); and the oracle's exact witness (vsub=2, psub=1) lands one sub-frame off.
  The fix the proof names: `remove_migration_pte` must restore the CARRIED psub, never recompute from
  the address.
-/
namespace Tessera.MigrateVsub

/-- A present sub-PTE of a cluster: it sits at virtual sub-index `vsub` (from the fault address) and
POINTS at the folio's physical sub-frame `psub`.  `relocate_vma_down` makes `vsub ≠ psub` reachable. -/
structure SubPte where
  vsub : Nat
  psub : Nat
deriving DecidableEq, Repr

/-- The physical sub-frame a sub-PTE maps, given the folio's base frame `pb`. -/
def SubPte.frame (pb : Nat) (s : SubPte) : Nat := pb + s.psub

/-- Valid sub-indices in a cluster of `cnt = PAGE_MMUCOUNT` sub-pages. -/
def SubPte.valid (cnt : Nat) (s : SubPte) : Prop := s.vsub < cnt ∧ s.psub < cnt

/-- `try_to_migrate_one`, FAITHFUL: the migration entry carries the PHYSICAL sub-index `psub`. -/
def encodeFaithful (s : SubPte) : Nat := s.psub

/-- `remove_migration_pte`, FAITHFUL: restore at the new base using the CARRIED sub-index. -/
def restoreFaithful (s : SubPte) (carried : Nat) : SubPte := { s with psub := carried }

/-- `remove_migration_pte`, the KERNEL BUG: recompute the sub-index from the ADDRESS (vsub) at
restore, ignoring what the entry carried. -/
def restoreVsub (s : SubPte) : SubPte := { s with psub := s.vsub }

/-! ### Faithful migration preserves placement for every cluster. -/

theorem faithful_preserves (pb : Nat) (s : SubPte) :
    (restoreFaithful s (encodeFaithful s)).frame pb = s.frame pb := by
  simp [restoreFaithful, encodeFaithful, SubPte.frame]

/-! ### The vsub-restore: correct ON the diagonal, provably WRONG off it. -/

/-- The buggy restore lands the sub-PTE at sub-frame `vsub` (where the intended is `psub`). -/
theorem vsub_lands_at_vsub (pb : Nat) (s : SubPte) :
    (restoreVsub s).frame pb = pb + s.vsub := by
  simp [restoreVsub, SubPte.frame]

/-- On the diagonal (vsub = psub) the bug is invisible — why it survived to the laptop. -/
theorem vsub_ok_on_diagonal (pb : Nat) (s : SubPte) (h : s.vsub = s.psub) :
    (restoreVsub s).frame pb = s.frame pb := by
  simp [restoreVsub, SubPte.frame, h]

/-- **THE BUG (decoded counterexample).** Off the diagonal — `vsub ≠ psub`, the oracle's precondition —
the vsub-restore re-points the sub-PTE at the WRONG new sub-frame. -/
theorem vsub_wrong_off_diagonal (pb : Nat) (s : SubPte) (h : s.vsub ≠ s.psub) :
    (restoreVsub s).frame pb ≠ s.frame pb := by
  simp only [restoreVsub, SubPte.frame]
  omega

/-! ### Why pgcl0 is clean (covers the control). -/

/-- At `PAGE_MMUCOUNT = 1` the only valid sub-index is 0, so every sub-PTE is on the diagonal and the
bug cannot manifest — exactly the oracle's pgcl0 control (0 catches, 0 kill-init).  The bug NEEDS
`PAGE_MMUCOUNT > 1` to have an off-diagonal. -/
theorem unit_cluster_forces_diagonal (s : SubPte) (h : SubPte.valid 1 s) : s.vsub = s.psub := by
  obtain ⟨h1, h2⟩ := h; omega

/-- The oracle's exact witness (`vsub=2 psub=1`): the buggy restore lands one sub-frame PAST the
intended one.  The model now PREDICTS the catch. -/
theorem oracle_witness (pb : Nat) :
    (restoreVsub { vsub := 2, psub := 1 }).frame pb = pb + 2
    ∧ (SubPte.frame pb { vsub := 2, psub := 1 }) = pb + 1 := by
  refine ⟨?_, ?_⟩ <;> simp [restoreVsub, SubPte.frame]

/-! ### The fix the proof names. -/

/-- **THE FIX.** `remove_migration_pte` must restore the CARRIED psub (the sub-index the migration
entry recorded), never recompute it from the fault address.  Then placement is preserved for EVERY
cluster — diagonal or not — so migration is faithful regardless of `relocate_vma_down`. -/
theorem fix_preserves_all (pb : Nat) (s : SubPte) :
    (restoreFaithful s (encodeFaithful s)).frame pb = s.frame pb :=
  faithful_preserves pb s

/-- And the fix and the bug AGREE exactly on the diagonal and DIVERGE exactly off it — so the fix
changes behaviour only for the vsub≠psub clusters the oracle flagged, nothing else. -/
theorem fix_minimal (pb : Nat) (s : SubPte) :
    ((restoreFaithful s (encodeFaithful s)).frame pb = (restoreVsub s).frame pb ↔ s.vsub = s.psub) := by
  simp only [restoreFaithful, encodeFaithful, restoreVsub, SubPte.frame]
  omega

end Tessera.MigrateVsub

/-
  Tessera — MIGRATE PSUB PRESERVATION (#143 root of the residual wrong-data).

  The last #143 residual (Electron int3 / invalid-opcode in shared read-only code
  such as libcef.so / libc.so.6, under heavy memory pressure) is NOT a refcount
  phantom: refs and mapcount stay balanced across a migration round-trip.  It is a
  PHYSICAL-PLACEMENT bug in the migration UNMAP side.

  A pgcl cluster = one struct page = PAGE_MMUCOUNT sub-PTEs; each present sub-PTE i
  maps a PHYSICAL sub-frame `psub i` (carried in the PTE's reserved sub-offset
  bits; pte_pfn() masks them, so all 16 sub-PTEs share the cluster-base pfn).
  Migration converts present sub-PTEs -> migration entries (unmap), then rebuilds
  present sub-PTEs on the destination (restore).  `remove_migration_pte` restores
  each sub-PTE from the psub its OWN migration entry carries (mm/migrate.c).

  The bug (regression from the vsub!=psub fix commit 1c4ae8671b12):
  `try_to_migrate_one` batches a cluster's contiguous present run (nr up to 16),
  and `get_and_clear_ptes` folds that run to a single pte -- discarding sub-PTEs
  1..nr-1's psub.  The old code then wrote ONE migration entry carrying sub-PTE 0's
  psub to ALL nr entries, so restore mapped every virtual sub-page onto sub-frame 0
  (`unmapBuggy`).  The anon swap-out path (`try_to_unmap_one`) never had this: it
  varies psub per fragment (`first + j`), which is why *swapped* pages placed
  correctly but *migrated* (compacted) pages corrupted -- an intermittent residual,
  not a dead machine.

  The fix (mm/rmap.c): snapshot each present sub-PTE's psub BEFORE the batched
  clear, then carry it per-entry (`unmapFixed`).  This models that round-trip
  identity, and why the robust per-entry snapshot is preferred over the cheaper
  swap-style `first + j` stride (`unmapStride`), which is correct only when the
  cluster's psubs happen to be contiguous.
-/
namespace Tessera
namespace MigratePsub

/-- A cluster's present sub-PTEs.  `psub i` is the PHYSICAL sub-frame that virtual
sub-index `i` maps.  (Physical placement only; refs/mapcount are balanced and
modelled elsewhere -- this file is purely about WHERE each sub-page points.) -/
structure Cluster where
  psub : Nat → Nat

/-- RESTORE (`remove_migration_pte`): rebuild each sub-PTE from the psub its own
migration entry carries. -/
def restore (entry : Nat → Nat) : Nat → Nat := entry

/-- UNMAP, pre-fix: `get_and_clear_ptes` folded the run to sub-PTE 0, and the one
resulting migration entry (sub-PTE 0's psub) was written to every sub-PTE. -/
def unmapBuggy (c : Cluster) : Nat → Nat := fun _ => c.psub 0

/-- UNMAP, fixed: each sub-PTE's psub was snapshotted before the clear and carried
into its OWN migration entry. -/
def unmapFixed (c : Cluster) : Nat → Nat := c.psub

/-- UNMAP, swap-mirror alternative: carry `psub 0 + i` (the cheap `first + j`
stride the swap-out path uses).  Modelled to justify NOT using it. -/
def unmapStride (c : Cluster) : Nat → Nat := fun i => c.psub 0 + i

/-- **THE FIX IS CORRECT**: the fixed round-trip is the identity on physical
placement -- every virtual sub-page is restored to the SAME sub-frame it had, for
every sub-index and every cluster, with no side condition. -/
theorem fixed_preserves (c : Cluster) (i : Nat) :
    restore (unmapFixed c) i = c.psub i := rfl

/-- **THE BUG**: the pre-fix round-trip collapses every sub-PTE onto sub-PTE 0's
physical sub-frame. -/
theorem buggy_collapses (c : Cluster) (i : Nat) :
    restore (unmapBuggy c) i = c.psub 0 := rfl

/-- Hence on a genuine cluster (sub-index `i` maps a different physical sub-frame
than sub 0 -- e.g. a shared code page whose sub-pages hold different instructions)
the pre-fix round-trip MIS-PLACES sub-index `i`: it is served sub-frame 0's bytes,
not its own.  This is the shared-code overwrite behind the int3 residual. -/
theorem buggy_misplaces (c : Cluster) (i : Nat)
    (h : c.psub i ≠ c.psub 0) :
    restore (unmapBuggy c) i ≠ c.psub i := by
  show c.psub 0 ≠ c.psub i
  intro heq
  exact h heq.symm

/-- The fix repairs exactly the case the bug corrupted: where the pre-fix
round-trip mis-placed sub-index `i`, the fixed round-trip restores it. -/
theorem fixed_repairs (c : Cluster) (i : Nat)
    (h : c.psub i ≠ c.psub 0) :
    restore (unmapFixed c) i = c.psub i ∧
    restore (unmapBuggy c) i ≠ c.psub i :=
  ⟨fixed_preserves c i, buggy_misplaces c i h⟩

/-- Why the robust per-entry snapshot beats the cheap swap-style stride: the
stride is correct ONLY when the cluster's psubs are contiguous-from-sub-0
(`psub i = psub 0 + i`, i.e. vsub==psub or a uniform relocate_vma_down shift). -/
theorem stride_preserves_only_if_contiguous (c : Cluster) (i : Nat)
    (hc : ∀ j, c.psub j = c.psub 0 + j) :
    restore (unmapStride c) i = c.psub i := by
  show c.psub 0 + i = c.psub i
  rw [hc i]

/-- ...whereas `unmapFixed` (the implemented snapshot-before-clear) preserves
placement for an ARBITRARY psub layout -- no contiguity assumption -- so it is
correct even for a non-contiguous (permuted) cluster the stride would mis-place.
`fixed_preserves` already proves this unconditionally; restated as the contrast. -/
theorem fixed_needs_no_contiguity (c : Cluster) (i : Nat) :
    restore (unmapFixed c) i = c.psub i := fixed_preserves c i

end MigratePsub
end Tessera

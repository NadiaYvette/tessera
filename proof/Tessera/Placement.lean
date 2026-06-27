/-
  Tessera — sub-page PLACEMENT correctness (pgcl #143 REDIRECT, 2026-06-27).

  pgcl's QEMU pgd-walk (an external observer reading *actual* page-table PTEs) OVERTURNED
  the free-while-mapped theory: `freed_while_mapped = 0` (4/4); freed pages read a normal
  `refcount:0 mapcount:-1`. So #143 is **NOT** a lifetime/refcount/orphan-PTE bug — the
  Property-2 `rmap_defer.v` / `no_free_while_referenced` and the cross-mm aggregate stand as
  general-safety results, but are not its mechanism.

  #143 is a **WRONG-DATA** corruption: init + forked children read the wrong CONTENT at
  consistent offsets → segv. The mechanism class is sub-page **PLACEMENT** — a cluster's
  sub-PTE pointing at the WRONG physical sub-page (a sub-offset *cross* / permutation), so
  userspace reads the wrong content. Catalog #9 (arm64 contpte sub-offset fold → wrong-page
  reads) and #15 (vm_pgoff↔vm_start sub-page assumption → wrong-sub-page copy).

  This file states and proves the obligation pgcl asked for, on the `Tile`/`grantsF`
  physical-translation model of `Frames.lean`:

      ∀ cluster (vb,pb), granule v present:  phys_subpage(v) = intended_subpage(v)

  and proves it PRESERVED across mprotect / fork (perms-only) and a CORRECT cow/migrate
  re-anchor — while a sub-offset-FOLDING cow (the #9/#15 bug) is a provable wrong-data error.
  This is precisely where formal verification beats pgcl's rig: the bug is KVM-timing but the
  structural observer is TCG-only, so the placement invariant can be settled without
  reproducing the race.
-/
import Tessera.Frames

namespace Tessera

/-- Intended physical frame for virtual granule `v` of a cluster at virtual base `vb`,
physical base frame `pb`: the **identity** sub-offset placement, `pb + (v - vb)`. -/
def intendedFrame (vb pb v : Nat) : Nat := pb + (v - vb)

/-- A tile is **correctly placed** in cluster `(vb, pb)` when it is anchored at the intended
physical sub-frame for its virtual base: `frame = pb + (base - vb)`. -/
def Tile.PlacedF (t : Tile) (vb pb : Nat) : Prop := t.frame = pb + (t.base - vb)

/-- **PLACEMENT CORRECTNESS** — the #143 redirect obligation. A correctly-placed, in-cluster
tile maps every present granule to its INTENDED physical sub-page: `phys = intended`, no
sub-page cross or permutation. -/
theorem placed_grantsF_intended {t : Tile} {vb pb v f : Nat} {p : Perm}
    (hpl : t.PlacedF vb pb) (hvb : vb ≤ t.base) (hg : t.grantsF v f p) :
    f = intendedFrame vb pb v := by
  obtain ⟨h1, _, hf, _⟩ := hg
  simp only [Tile.PlacedF] at hpl
  simp only [intendedFrame]
  omega

/-- mprotect / fork-write-protect: only `perms` change; the physical anchor (`frame`, `base`)
is untouched. -/
def Tile.setPerms (t : Tile) (p : Perm) : Tile := { t with perms := p }

/-- **mprotect preserves placement** — it changes permissions, never the physical anchor, so
it cannot move content to the wrong sub-page. -/
theorem setPerms_preserves_placed {t : Tile} {vb pb : Nat} {p : Perm}
    (h : t.PlacedF vb pb) : (t.setPerms p).PlacedF vb pb := by
  simpa [Tile.setPerms, Tile.PlacedF] using h

/-- **fork preserves placement** — fork write-protects the parent's mapping (a perms change),
so the child reads exactly the SAME physical sub-pages as the parent (no cross). -/
theorem fork_preserves_placed {t : Tile} {vb pb : Nat} (wp : Perm)
    (h : t.PlacedF vb pb) : (t.setPerms wp).PlacedF vb pb :=
  setPerms_preserves_placed h

/-- A **CORRECT cow / migration re-anchor**: copy the cluster to a new physical base `npb`,
KEEPING the sub-offset — `frame := npb + (base - vb)`. -/
def Tile.cowRemap (t : Tile) (vb npb : Nat) : Tile := { t with frame := npb + (t.base - vb) }

/-- **A correct cow / migrate preserves placement** (in the new physical base): the right
sub-page's content reaches the right virtual sub-page. -/
theorem cowRemap_preserves_placed {t : Tile} (vb npb : Nat) :
    (t.cowRemap vb npb).PlacedF vb npb := by
  simp [Tile.cowRemap, Tile.PlacedF]

/-- **The #9 / #15 bug**: a cow / fault / fold that anchors at the new base but DROPS the
sub-offset — `frame := npb` — ignoring that the cluster is mapped at sub-offset `base - vb`. -/
def Tile.cowFold (t : Tile) (npb : Nat) : Tile := { t with frame := npb }

/-- **The sub-offset-folding cow is a provable WRONG-DATA error**: whenever the cluster is
mapped at a nonzero sub-offset (`vb < base`), the folded tile maps its base granule to the
WRONG physical sub-page (`phys ≠ intended`) — userspace reads the wrong content. This is the
#143 wrong-data signature as a non-theorem of placement. -/
theorem cowFold_wrong_data {t : Tile} {vb npb : Nat}
    (hsub : vb < t.base) (hsz : 0 < t.size) :
    ∃ v f, (t.cowFold npb).grantsF v f t.perms ∧ f ≠ intendedFrame vb npb v := by
  refine ⟨t.base, npb, ⟨Nat.le_refl _, ?_, ?_, rfl⟩, ?_⟩
  · simp only [Tile.cowFold]; omega
  · simp only [Tile.cowFold]; omega
  · simp only [intendedFrame]; omega

/-- And dually: the folding bug also **breaks the placement predicate** itself (it is not a
correctly-placed tile) at any nonzero sub-offset. -/
theorem cowFold_breaks_placed {t : Tile} {vb npb : Nat} (hsub : vb < t.base) :
    ¬ (t.cowFold npb).PlacedF vb npb := by
  simp only [Tile.cowFold, Tile.PlacedF]
  omega

end Tessera

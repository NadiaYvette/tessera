/-
  Tessera — the sub-page PERMUTATION π, and #143 Bug 2 (rematerialize-in placement).

  pgcl `143-empirical-to-tessera.md` (round 4) SPLIT #143 into two content-motion bugs and, decisively,
  showed the residual one breaks the assumption every earlier wrong-data module baked in: that a
  cluster's virtual sub-offset equals its physical sub-offset (`vsub == psub`). It need not.
  `mremap` / `relocate_vma_down` move a cluster's PTEs by a non-cluster-aligned delta: the PTE keeps
  its physical sub-offset (psub) but gets a NEW virtual sub-offset (vsub). So a cluster carries a
  PERMUTATION π : vsub ↦ psub, normally identity but not always (the relocated PID1 stack:
  vsub=0x2000, psub=0x1000, fired 6/6 on the oracle).

  The present mapping carries psub in the PTE (`pte_suboffset`); COW (`wp_page_copy`) and fork
  (`copy_present_page`) read it and preserve π — they are CORRECT. The two rematerialize-IN paths do
  NOT: `do_swap_page` and `remove_migration_pte` reconstruct psub from the faulting VADDR (the vsub),
  assuming π = identity. That is Bug 2. This file makes π first-class, proves the π-carrying
  rematerialize correct for ANY π, and proves the vaddr-reconstructing one wrong exactly on
  `vsub ≠ psub` — pgcl's general localization. It also models Bug 1 (completeness) and both candidate
  fixes, to back the spec-authority call (see `doc/to-pgcl-143-direction.md` §8).
-/
import Tessera.Eviction

namespace Tessera

-- A cluster's sub-page permutation `π : vsub ↦ psub` (a function `Nat → Nat`). Normally identity;
-- non-cluster-aligned virtual motion (`mremap`, `relocate_vma_down`) makes it non-identity.

/-- The physical frame backing virtual granule `v` of cluster `(vb, pb)` under permutation `π`:
`pb + π(v − vb)`. With `π = id` this is `Placement.intendedFrame` — the assumption every earlier
module made. -/
def framePi (vb pb : Nat) (π : Nat → Nat) (v : Nat) : Nat := pb + π (v - vb)

/-- The intended content at `v` *preserving π*: the content of the physical sub-frame π names. -/
def intendedPi (vb pb : Nat) (π : Nat → Nat) (mem : Mem) (v : Nat) : Content :=
  mem (framePi vb pb π v)

/-- **Faithful rematerialize-in PRESERVES π** (Option 1, and what COW/fork already do): an edge that
carries the source sub-offset `psub = π(vsub)` — as the present PTE does via `pte_suboffset` —
restores each granule to its correct physical sub-frame, for ANY π. No canonicalization, no copy. -/
theorem framePi_faithful (vb pb : Nat) (π : Nat → Nat) (mem : Mem) (v : Nat) :
    observed (framePi vb pb π) mem v = intendedPi vb pb π mem v :=
  rfl

/-- **Bug 2 — the identity assumption.** `do_swap_page` / `remove_migration_pte` reconstruct the
physical sub-offset from the VIRTUAL one (`vsub = v − vb`), i.e. they use `pb + (v − vb)`. -/
def frameIdentity (vb pb : Nat) (v : Nat) : Nat := pb + (v - vb)

/-- **THE general theorem (pgcl's localization of Bug 2)**: reconstructing the physical sub-offset
from the vaddr (vsub) rather than the source (psub = π(vsub)) lands content on the WRONG physical
sub-frame for every granule where `vsub ≠ psub`. Hence swap-in / migration-in are wrong exactly on
`vsub ≠ psub` clusters, while COW / fork (which read psub from the source) are correct. -/
theorem reconstruct_from_vaddr_wrong {vb pb : Nat} {π : Nat → Nat} {v : Nat}
    (hperm : π (v - vb) ≠ v - vb) :
    frameIdentity vb pb v ≠ framePi vb pb π v := by
  simp only [frameIdentity, framePi]
  omega

/-- …and at the observable: the identity-assuming rematerialize reads the WRONG content whenever the
crossed sub-frames differ — the residual #143 anon segv (`init[1]: segfault at 0`). -/
theorem identity_remat_observed_wrong {vb pb : Nat} {π : Nat → Nat} {mem : Mem} {v : Nat}
    (hdiff : mem (pb + (v - vb)) ≠ mem (pb + π (v - vb))) :
    observed (frameIdentity vb pb) mem v ≠ intendedPi vb pb π mem v := by
  simp only [observed, frameIdentity, intendedPi, framePi]
  exact hdiff

/-- **Option 2 — canonicalize π to identity.** `relocate`/`mremap` copies content to a fresh cluster
so π becomes identity; afterwards the identity-assuming rematerialize is correct by construction —
`frameIdentity = framePi id`, so the existing (identity-assuming) models become sound. The cost is a
copy on relocate; the benefit is the spec needs no π. -/
theorem canonicalized_identity_ok (vb pb : Nat) (v : Nat) :
    frameIdentity vb pb v = framePi vb pb id v := by
  simp [frameIdentity, framePi]

/-- **Bug 1 — completeness (swap-OUT).** swap-out must emit an entry for EVERY mapped sub-PTE. The
PGCL Option-A quirk wrote ONE entry and left the rest `pte_none` → they refault as ZERO. Modeled: a
swap-out covering only sub-index set `S` makes sub-pages outside `S` rematerialize as 0. -/
def evictCover (S : Nat → Bool) (sv : Nat → Content) : Nat → Content :=
  fun i => if S i then sv i else 0

/-- **The one-entry swap-out loses data**: covering only sub-0, every other sub-page refaults as
zero — 15/16 of every reclaimed cluster's content. The obligation: `|entries| = |present sub-PTEs|`
(cover all), which this buggy form violates. -/
theorem evict_oneEntry_loses_data {sv : Nat → Content} (hnz : sv 1 ≠ 0) :
    evictCover (fun i => i == 0) sv 1 ≠ sv 1 := by
  have h : evictCover (fun i => i == 0) sv 1 = 0 := by simp [evictCover]
  rw [h]
  exact fun he => hnz he.symm

end Tessera

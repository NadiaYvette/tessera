/-
  Tessera — clustered virtual-memory manager: Layer A (Algorithm), core model.

  See ../doc/tessera-verification-kickoff.md.  This file establishes the data on
  which the whole development reasons: extents, their well-formedness, and the
  disjointness relation that makes an extent *set* a coherent address space.

  ## Nomenclature (kickoff §10)

  Two quantities mainstream systems conflate are kept distinct:

  * **Minimum Mapping Granularity (MMG)**, size `M`: the smallest region the MMU
    can describe with one translation (smallest hardware page / TLB entry).
  * **Kernel Allocation Unit (KAU)**, size `P = c · M`: the smallest chunk of
    physical memory the allocator hands out, for a power-of-two cluster factor
    `c ≥ 1`.

  ## Units

  All addresses and sizes here are measured in **units of `M`** (granules).  The
  structural invariants of Layer A — disjointness, alignment, power-of-two
  sizing, tiling under `split` — are scale-invariant: they are facts about
  granule counts and do not depend on `M`'s byte size, which enters only at
  Layer S (the ABI spec) and Layer I (concrete PTE encodings).  Working in
  granule units keeps the arithmetic about powers of two, where it belongs.

  The cluster factor `c` (hence `P = c·M`) and the KAU-integrity invariant
  (invariant 2) are introduced with the superpage operations in M2; M1 concerns
  invariant 1 (disjoint, aligned, power-of-two-sized extents) and `split`.
-/

namespace Tessera

/-- Permissions on a mapped region.  Carried by every extent: an extent has, by
construction, *uniform* permissions over its whole range — the precondition that
makes a superpage legal (invariant 3, M2).  For M1 they are merely transported by
`split`. -/
structure Perm where
  read  : Bool
  write : Bool
  exec  : Bool
deriving DecidableEq, Repr

/-- An **extent** (kickoff §2, Layer A): an aligned, power-of-two-sized run of
granules with uniform permissions.  `base` and `size` are granule counts (units
of `M`).  An extent is the unit at which Layer A reasons; it may ultimately be
mapped either by a single superpage TLB entry or by a vector of `M`-grained
entries, but that choice is invisible here and to the ABI (the M3 theorem). -/
structure Extent where
  base  : Nat
  size  : Nat
  perms : Perm
deriving DecidableEq, Repr

namespace Extent

/-- Low end of the half-open granule interval `[lo, hi)` the extent covers. -/
def lo (e : Extent) : Nat := e.base

/-- High end (exclusive) of the granule interval `[lo, hi)` the extent covers. -/
def hi (e : Extent) : Nat := e.base + e.size

end Extent

/-- `n` is a power of two. -/
def IsPow2 (n : Nat) : Prop := ∃ k : Nat, n = 2 ^ k

/-- A power of two is positive — so every valid extent is non-empty. -/
theorem IsPow2.pos {n : Nat} (h : IsPow2 n) : 0 < n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => decide
  | succ k ih =>
      have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
      omega

/-- **Well-formedness of a single extent** (kickoff invariant 1): its size is a
power of two (a power-of-two multiple of `M`, in granule units), and its base is
aligned to its size. -/
def Extent.Valid (e : Extent) : Prop :=
  IsPow2 e.size ∧ e.size ∣ e.base

theorem Extent.Valid.size_pos {e : Extent} (h : e.Valid) : 0 < e.size :=
  IsPow2.pos h.1

/-- Two extents are **disjoint** when their half-open granule intervals do not
overlap.  Symmetric (`Disjoint.symm`). -/
def Disjoint (a b : Extent) : Prop :=
  a.hi ≤ b.lo ∨ b.hi ≤ a.lo

theorem Disjoint.symm {a b : Extent} (h : Disjoint a b) : Disjoint b a := by
  simp only [Disjoint, Extent.lo, Extent.hi] at h ⊢; omega

/-- **Well-formedness of an extent set** (kickoff invariant 1, set level): every
extent is valid, and the extents are pairwise disjoint.  An extent set models the
mapped portion of an address space; this predicate is the thing every operation
must preserve. -/
def WF (es : List Extent) : Prop :=
  (∀ e ∈ es, e.Valid) ∧ es.Pairwise Disjoint

end Tessera

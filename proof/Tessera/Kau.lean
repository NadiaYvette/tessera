/-
  Tessera — Layer A / M2: the KAU and its PTE-vector (Rung 1 of the abstraction
  ladder in ../doc/proof-obligations.md).

  A **kernel allocation unit (KAU)** of size `P = c·M` is tracked, at the finer
  granularity, as a **vector of `c` per-`M` slots** — each present (a sub-PTE) or
  absent (the "partially populated" state). This file is the *local* model: one
  address space's view of one KAU. It establishes:

    * invariant 2 (KAU integrity): the vector has `c` slots — one per constituent
      `M`-page — and the base is `P`-aligned; the `c` slots correspond, by
      construction (the allocator hands out contiguous `P`-aligned KAUs), to the `c`
      contiguous `M`-pages `[base, base+c)` (see ../doc/clustering-rationale.md);
    * invariant 5 (dirty/referenced aggregation): the per-KAU dirty/referenced
      answer is the **OR over the `c` per-`M` bits** — *not* a peek at slot 0
      (the pgcl #20 bug class).

  The *global* shared-object mapcount/refcount (Rung 2) and the intra-KAU tiling /
  superpage realization (category E; ../doc/intra-kau-tiling.md) are layered on top;
  neither affects this file.
-/
import Tessera.Basic

namespace Tessera

/-- A per-`M` sub-PTE: the translation state of one `M`-granule within a KAU. -/
structure SubPte where
  frame : Nat
  perms : Perm
  dirty : Bool
  ref   : Bool
deriving DecidableEq, Repr

/-- A slot of a KAU's PTE-vector: `some` (present) or `none` (absent — the
partially-populated state). -/
abbrev Slot := Option SubPte

/-- Whether a slot is present. -/
def Slot.present (s : Slot) : Bool := s.isSome

/-- A slot's dirty bit (`false` if absent). -/
def Slot.dirty : Slot → Bool
  | none => false
  | some p => p.dirty

/-- A slot's referenced bit (`false` if absent). -/
def Slot.ref : Slot → Bool
  | none => false
  | some p => p.ref

/-- A **KAU**: a `P`-aligned granule `base` and its vector of `c` per-`M` `slots`. -/
structure Kau where
  base  : Nat
  slots : List Slot
deriving Repr

namespace Kau

/-- **Invariant 2 (KAU integrity)** for cluster factor `c`: the PTE-vector has exactly
`c` slots (one per constituent `M`-page), and the base is `P = c·M`-aligned. The `c`
slots correspond, by construction, to the `c` contiguous `M`-pages `[base, base+c)`. -/
def WF (c : Nat) (k : Kau) : Prop :=
  k.slots.length = c ∧ c ∣ k.base

/-- **Invariant 5**: per-KAU dirty is the OR over the `c` per-`M` dirty bits. -/
def dirty (k : Kau) : Bool := k.slots.any Slot.dirty

/-- **Invariant 5**: per-KAU referenced is the OR over the `c` per-`M` ref bits. -/
def referenced (k : Kau) : Bool := k.slots.any Slot.ref

/-- This view's contribution to the backing object's mapcount: the number of present
sub-PTEs. (The *global* mapcount across address spaces is Rung 2.) -/
def localMapcount (k : Kau) : Nat := (k.slots.filter Slot.present).length

/-- Update one slot of the PTE-vector. -/
def setSlot (k : Kau) (i : Nat) (s : Slot) : Kau := { k with slots := k.slots.set i s }

/-- Per-KAU dirty is honest: it is `true` exactly when *some* slot is dirty — not a
function of slot 0 alone (the pgcl #20 failure mode is unrepresentable). -/
theorem dirty_iff (k : Kau) : k.dirty = true ↔ ∃ s ∈ k.slots, Slot.dirty s = true := by
  simp [Kau.dirty, List.any_eq_true]

/-- A single dirty sub-PTE forces the whole KAU dirty (the OR is real). -/
theorem dirty_of_mem {k : Kau} {s : Slot} (h : s ∈ k.slots) (hd : Slot.dirty s = true) :
    k.dirty = true := by
  simp only [Kau.dirty, List.any_eq_true]; exact ⟨s, h, hd⟩

/-- Likewise for referenced. -/
theorem referenced_of_mem {k : Kau} {s : Slot} (h : s ∈ k.slots) (hr : Slot.ref s = true) :
    k.referenced = true := by
  simp only [Kau.referenced, List.any_eq_true]; exact ⟨s, h, hr⟩

/-- **Invariant 2 is preserved by a slot update**: setting a slot keeps the vector
length `c` (so still `c` per-`M` slots) and does not move the base. -/
theorem WF.setSlot {c : Nat} {k : Kau} (h : WF c k) (i : Nat) (s : Slot) :
    WF c (k.setSlot i s) := by
  obtain ⟨hlen, halign⟩ := h
  refine ⟨?_, halign⟩
  show (k.slots.set i s).length = c
  rw [List.length_set]; exact hlen

end Kau

/-! ### Smoke test -/

/-- A 4-slot KAU (c = 4) at base 8 with one dirty middle slot: well-formed, and the
per-KAU dirty bit is `true` by aggregation even though slot 0 is clean. -/
example :
    let rw : Perm := ⟨true, true, false⟩
    let k : Kau := ⟨8, [none, some ⟨0, rw, true, false⟩, none, none]⟩
    Kau.WF 4 k ∧ k.dirty = true := by
  refine ⟨⟨rfl, ⟨2, rfl⟩⟩, ?_⟩
  decide

end Tessera

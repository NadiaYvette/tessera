/-
  Tessera — Layer I (the hardware leaf): the **PTE bit-encoding**.  The Layer-A leaf is a
  `(valid, permission, physical frame)` triple (`Frames.lean`/`Kau.lean`'s `SubPte`); the
  hardware stores it as a packed descriptor *word*.  This file models that packing and
  proves the encoding **realizes** the Layer-A leaf — `decode ∘ encode = id` on every
  field — and that a layout whose frame field **overlaps** a flag bit provably corrupts
  the translation (the PTE field-aliasing bug class).

  Layout (a generic 64-bit-style descriptor, in granule-address form):
    bit 0   = valid;  bits 1,2,3 = R,W,X;  bits 12.. = physical frame number (PFN).
  So a flag occupies the low 12 bits and the frame is `frame · 4096`, disjoint by
  construction — which is exactly what the round-trip theorems certify.
-/
import Tessera.Basic

namespace Tessera
namespace Pte

/-- A page-table entry as the hardware sees it: one descriptor word. -/
structure Pte where
  word : Nat
deriving Repr, DecidableEq

/-- **Encode** a `(valid, perm, frame)` leaf into a descriptor word: flags in the low
12 bits, the frame above. -/
def encode (valid : Bool) (p : Perm) (frame : Nat) : Pte :=
  ⟨(if valid then 1 else 0) + (if p.read then 2 else 0) + (if p.write then 4 else 0)
     + (if p.exec then 8 else 0) + frame * 4096⟩

def decValid (pte : Pte) : Bool := pte.word % 2 == 1
def decRead  (pte : Pte) : Bool := pte.word / 2 % 2 == 1
def decWrite (pte : Pte) : Bool := pte.word / 4 % 2 == 1
def decExec  (pte : Pte) : Bool := pte.word / 8 % 2 == 1
def decFrame (pte : Pte) : Nat := pte.word / 4096
def decPerm  (pte : Pte) : Perm := ⟨decRead pte, decWrite pte, decExec pte⟩

/-- **The frame round-trips**: the descriptor decodes to exactly the encoded frame. -/
theorem decFrame_encode (v : Bool) (p : Perm) (f : Nat) : decFrame (encode v p f) = f := by
  obtain ⟨r, w, x⟩ := p
  cases v <;> cases r <;> cases w <;> cases x <;> simp [decFrame, encode] <;> omega

/-- **The valid bit round-trips**. -/
theorem decValid_encode (v : Bool) (p : Perm) (f : Nat) : decValid (encode v p f) = v := by
  obtain ⟨r, w, x⟩ := p
  cases v <;> cases r <;> cases w <;> cases x <;> simp [decValid, encode] <;> omega

/-- **The permissions round-trip**: the descriptor decodes to exactly the encoded perms.
With `decFrame_encode` and `decValid_encode`, the encoding fully realizes the Layer-A
`(valid, perm, frame)` leaf — no field corrupts another. -/
theorem decPerm_encode (v : Bool) (p : Perm) (f : Nat) : decPerm (encode v p f) = p := by
  obtain ⟨r, w, x⟩ := p
  cases v <;> cases r <;> cases w <;> cases x <;>
    simp [decPerm, decRead, decWrite, decExec, encode] <;> omega

/-- A **buggy layout** that shifts the frame by only 3 bits (×8) — colliding with the
exec flag (bit 3). -/
def encodeBuggy (valid : Bool) (p : Perm) (frame : Nat) : Pte :=
  ⟨(if valid then 1 else 0) + (if p.read then 2 else 0) + (if p.write then 4 else 0)
     + (if p.exec then 8 else 0) + frame * 8⟩

/-- **Field overlap corrupts the translation — a provable error.** With the frame at
×8 it aliases the exec bit, so the decoded exec permission depends on the *frame*, not
on the encoded permission: encoding a non-executable page with an odd frame decodes as
executable. The disjoint-field layout (`encode`) is necessary. -/
theorem encodeBuggy_corrupts :
    ∃ (v : Bool) (p : Perm) (f : Nat), decExec (encodeBuggy v p f) ≠ p.exec := by
  refine ⟨false, ⟨false, false, false⟩, 1, ?_⟩
  decide

end Pte
end Tessera

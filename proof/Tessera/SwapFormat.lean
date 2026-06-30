/-
  Tessera — the swap-PTE FORMAT obligation (the SWP_OFFSET_FIRST_BIT change).

  Permute/SwapEntry prove the ABSTRACT round-trip: IF a migration/swap entry carries psub, the
  restore is faithful.  This module discharges the CONCRETE precondition that made carrying psub
  possible at all: a swap-PTE word has an offset lane (swap slot / migration pfn, stride `S`) and a
  low sub-offset lane (the carried psub, stride `subS`, `cnt` values wide).  The kernel change raised
  SWP_OFFSET_FIRST_BIT to PAGE_SHIFT so the offset lane sits ABOVE the sub-offset lane: `S = cnt*subS`.

  Proved: with `S = cnt*subS` BOTH fields round-trip (offset unperturbed by a carried sub-index, and
  the sub-index recovered exactly) — so the format is lossless.  And the OLD format (offset lane
  starting below the top of the sub-offset lane, S < cnt*subS) provably COLLIDES: a nonzero carried
  sub-index corrupts the decoded offset.  This is the up-front invariant the 2003 formulation
  rigidly demanded; it is independent of whether carrying psub moves the kill-init metric.

  (Real instantiation: subS = 2^MMUPAGE_SHIFT = 4096, cnt = PAGE_MMUCOUNT = 16, S = 2^PAGE_SHIFT
  = 65536 = 16*4096; OLD S = 2^9 = 512 < 65536.)
-/
namespace Tessera.SwapFormat

/-- Pack an offset and a sub-index into one swap-PTE word: offset in its lane (stride `S`),
    sub-index in the low sub-offset lane (stride `subS`). -/
def packSwp (S subS off sub : Nat) : Nat := off * S + sub * subS

/-- Decode the offset lane. -/
def unpackOff (S x : Nat) : Nat := x / S

/-- Decode the `cnt`-wide sub-offset lane. -/
def unpackSub (subS cnt x : Nat) : Nat := (x / subS) % cnt

/-- A key rewrite: the packed word factors through `subS` when the offset lane is `cnt*subS`. -/
private theorem pack_factor (subS cnt off sub : Nat) :
    packSwp (cnt * subS) subS off sub = subS * (off * cnt + sub) := by
  unfold packSwp
  rw [Nat.mul_add]
  congr 1
  · rw [Nat.mul_comm subS (off * cnt), Nat.mul_assoc]
  · rw [Nat.mul_comm]

/-- FAITHFUL FORMAT — offset lane recovered exactly, undisturbed by the carried sub-index. -/
theorem unpackOff_faithful {subS cnt off sub : Nat} (hs : 0 < subS) (hsub : sub < cnt) :
    unpackOff (cnt * subS) (packSwp (cnt * subS) subS off sub) = off := by
  unfold unpackOff packSwp
  have hlt : sub * subS < cnt * subS := Nat.mul_lt_mul_of_pos_right hsub hs
  have hk : 0 < cnt * subS := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  rw [Nat.mul_comm off (cnt * subS), Nat.mul_add_div hk, Nat.div_eq_of_lt hlt, Nat.add_zero]

/-- FAITHFUL FORMAT — the carried sub-index is recovered exactly. -/
theorem unpackSub_faithful {subS cnt off sub : Nat} (hs : 0 < subS) (hsub : sub < cnt) :
    unpackSub subS cnt (packSwp (cnt * subS) subS off sub) = sub := by
  unfold unpackSub
  rw [pack_factor, Nat.mul_div_cancel_left _ hs, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hsub]

/-- Both lanes round-trip together: the format is a faithful pairing. -/
theorem format_roundtrip {subS cnt off sub : Nat} (hs : 0 < subS) (hsub : sub < cnt) :
    unpackOff (cnt * subS) (packSwp (cnt * subS) subS off sub) = off ∧
    unpackSub subS cnt (packSwp (cnt * subS) subS off sub) = sub :=
  ⟨unpackOff_faithful hs hsub, unpackSub_faithful hs hsub⟩

/-- The real instantiation (subS=4096, cnt=16, S=65536): a psub of 5 rides under any slot offset
    and is recovered, with the offset untouched. -/
theorem format_roundtrip_real (off : Nat) :
    unpackOff 65536 (packSwp 65536 4096 off 5) = off ∧
    unpackSub 4096 16 (packSwp 65536 4096 off 5) = 5 :=
  format_roundtrip (subS := 4096) (cnt := 16) (by decide) (by decide)

/-- COLLISION in the OLD format (SWP_OFFSET_FIRST_BIT = 9, S = 512 < 16*4096): a nonzero carried
    sub-index corrupts the decoded offset.  Concrete witness: off=1, sub=1 decodes to offset 9. -/
theorem old_format_collides : unpackOff 512 (packSwp 512 4096 1 1) = 9 := by decide

theorem old_format_not_faithful : unpackOff 512 (packSwp 512 4096 1 1) ≠ 1 := by decide

end Tessera.SwapFormat

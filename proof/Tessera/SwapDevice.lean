/-
  Tessera — SWAP DEVICE slot accounting (pgcl #143 task #21: the zram 16x over-count).

  A swap device of `bytes` capacity is carved into slots at the MMUPAGE (4KB) granule -- each
  4KB sub-MMUPAGE owns one swap slot (kernel `folio_dup_swap`: one swap ref per MMUPAGE slot;
  `read_swap_header`: `swapfilepages = i_size >> MMUPAGE_SHIFT`).  A 64KB cluster folio spans
  `MMUCOUNT` (= PAGE_MMUCOUNT = 16) contiguous slots (`folio_swap_order = folio_order +
  PAGE_MMUSHIFT`), allocated/freed as one block.

  THE INVARIANT the swap layer must satisfy: the enabled slot count equals the device capacity
  in MMUPAGE units, `slots = bytes / MMUPAGE`.  The observed zram bug enabled `MMUCOUNT x`
  that -- a PAGE_SHIFT-for-MMUPAGE_SHIFT confusion (the disk swap FILES are correct; only the
  block device `/dev/zram0` over-counted, 8GB device -> 128GB swap).  This file proves the
  correct count exactly fits and the 16x count over-commits the device by MMUCOUNT -- i.e. the
  swap layer would write past the device end (corruption / OOM).
-/
namespace Tessera
namespace SwapDevice

/-- MMUPAGE_SIZE: the hardware page and the swap-slot granule (4KB). -/
def MMUPAGE : Nat := 4096
/-- PAGE_MMUCOUNT: sub-MMUPAGE swap slots per 64KB cluster folio. -/
def MMUCOUNT : Nat := 16
/-- PAGE_SIZE: the kernel cluster (64KB) = MMUPAGE * MMUCOUNT. -/
def CLUSTER : Nat := MMUPAGE * MMUCOUNT

/-- A swap device / area, by capacity in bytes. -/
structure Dev where
  bytes : Nat
deriving Repr, DecidableEq

/-- **CORRECT** slot count: one 4KB slot per 4KB of capacity (`i_size >> MMUPAGE_SHIFT`). -/
def slots (d : Dev) : Nat := d.bytes / MMUPAGE

/-- **BUGGY** slot count: MMUCOUNT (16) x the correct slots -- the observed zram over-count,
a PAGE_SHIFT-for-MMUPAGE_SHIFT confusion in the block-device swap-size path. -/
def slotsBug (d : Dev) : Nat := MMUCOUNT * slots d

/-- The over-count is exactly the cluster factor. -/
theorem slotsBug_is_16x (d : Dev) : slotsBug d = 16 * slots d := rfl

/-- **CORRECT FITS**: the true slot count times the slot size equals the device capacity --
the area exactly covers the device, no more. -/
theorem slots_fits (d : Dev) (h : MMUPAGE ∣ d.bytes) : slots d * MMUPAGE = d.bytes := by
  unfold slots
  exact Nat.div_mul_cancel h

/-- **THE BUG OVER-COMMITS**: the 16x count claims MMUCOUNT times the device's real bytes, so
the swap layer commits slots the device cannot hold -> writes past the end.  The safety
violation behind the "reports more swap than exists". -/
theorem slotsBug_overcommits (d : Dev) (h : MMUPAGE ∣ d.bytes) (hpos : 0 < d.bytes) :
    slotsBug d * MMUPAGE = 16 * d.bytes ∧ d.bytes < slotsBug d * MMUPAGE := by
  have hf : slots d * MMUPAGE = d.bytes := slots_fits d h
  have key : slotsBug d * MMUPAGE = 16 * d.bytes := by
    unfold slotsBug MMUCOUNT
    rw [Nat.mul_assoc, hf]
  refine ⟨key, ?_⟩
  rw [key]; omega

/-- **CORRECT NEVER over-commits** (the contrast): the true count fits the device exactly. -/
theorem slots_no_overcommit (d : Dev) (h : MMUPAGE ∣ d.bytes) :
    slots d * MMUPAGE ≤ d.bytes := Nat.le_of_eq (slots_fits d h)

/-! ## Cluster ⇄ slot accounting: a cluster is MMUCOUNT contiguous slots -/

/-- **CLUSTER-SLOT IDENTITY**: for a device that is a whole number `k` of 64KB clusters, the
correct slot count is exactly `MMUCOUNT * k` -- so a per-cluster swap alloc/free (MMUCOUNT
slots as one block, `folio_swap_order = order + PAGE_MMUSHIFT`) tiles the area with no
remainder. -/
theorem slots_eq_clusters_scaled (d : Dev) (k : Nat) (hk : d.bytes = CLUSTER * k) :
    slots d = MMUCOUNT * k := by
  unfold slots MMUPAGE
  rw [hk]
  unfold CLUSTER MMUPAGE MMUCOUNT
  rw [Nat.mul_assoc]
  exact Nat.mul_div_cancel_left _ (by omega)

/-! ## The concrete r4da case: zram0 = 8 GiB device, buggy swap = 128 GiB -/

/-- The laptop's zram0: 8 GiB capacity (config `zram-size = min(ram, 8192)`). -/
def zram0 : Dev := ⟨8589934592⟩

/-- Correct: 2,097,152 slots = 8 GiB. -/
theorem zram0_slots : slots zram0 = 2097152 := by decide

/-- Buggy: 33,554,432 slots = 128 GiB = 16x -- exactly what swapon enabled (`134217664k`). -/
theorem zram0_slotsBug : slotsBug zram0 = 33554432 := by decide

end SwapDevice
end Tessera


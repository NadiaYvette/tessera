/-
  Tessera — RMAP ADD/REMOVE CALL-BALANCE: the #143 obligation, per pgcl R13's faithful-laptop A/B.

  R13 (`doc/from-pgcl-143-cbmc.md`) settled the diagnosis with two probed kernels booted on the real
  ThinkPad (the FAITHFUL judge). The `_mapcount < -1` over-remove is real and frequent — and, decisively,
  it is UPSTREAM OF and INDEPENDENT OF the free: B2's over-removed page was *allocated, refcount 10, not
  freed*. So the bug is NOT a lifetime race. This refutes, on the faithful judge, BOTH:
    * R11's free-while-mapped / `folio_mapped()` deferred-put gate (WARN 0×; B2 had MORE over-removes), and
    * R12's incarnation/ABA framing (the reincarnation was a correlate, not the cause).
  It is a DETERMINISTIC COUNT IMBALANCE.

  Mechanism: zap removes rmap once per present sub-PTE (`#removes == #present-sub-PTEs`), so the underflow
  means the INSTALL side issued FEWER `folio_add_rmap_pte` calls than there are present sub-PTEs. The
  obligation is therefore the rmap ADD/REMOVE CALL-BALANCE, and R13's prime suspect is the `vsub != psub`
  batching edge — `pgcl_pte_batch` groups by PHYSICAL sub-index, while `mremap`/`relocate_vma_down` make
  vsub ≠ psub — the exact permutation π this project already made first-class in `Permute.lean`.

  This file: states the call-balance invariant; proves the balanced operations preserve it; proves that
  ANY install under-add drives a subsequent CORRECT zap below zero — the over-remove, with NO free in the
  model (the formal form of R13 verdict 2); and localizes the under-add to a non-identity π, tying it to
  `Permute.migsub_observed_case` and R13's anchor `mc = -2`.
-/
import Tessera.Permute

namespace Tessera

/-- A cluster folio's rmap accounting. `mapcount` = Linux `_mapcount + 1` (the number of mappings;
fully-unmapped is `_mapcount = -1`, i.e. `mapcount = 0`). `present` = the true number of present sub-PTEs
mapping the folio across all mms. -/
structure Rmap where
  mapcount : Int
  present  : Int
deriving Repr

/-- **THE OBLIGATION (R13): the rmap add/remove CALL-BALANCE** — `_mapcount + 1 == Σ present sub-PTEs`. -/
def Rmap.Balanced (r : Rmap) : Prop := r.mapcount = r.present

/-- A fresh (never-mapped) folio. -/
def Rmap.fresh : Rmap := { mapcount := 0, present := 0 }

theorem fresh_balanced : Rmap.fresh.Balanced := rfl

/-- **install** a batch: `kpte` sub-PTEs become present and the install issues `kadd` rmap-adds
(`folio_add_rmap_pte(s)`). -/
def Rmap.install (r : Rmap) (kadd kpte : Int) : Rmap :=
  { mapcount := r.mapcount + kadd, present := r.present + kpte }

/-- **zap** a batch: `j` present sub-PTEs are removed and zap issues exactly `j` rmap-removes — R13
confirmed the zap side is correct (removes once per present sub-PTE). -/
def Rmap.zap (r : Rmap) (j : Int) : Rmap :=
  { mapcount := r.mapcount - j, present := r.present - j }

/-- **Install preserves balance IFF it adds one rmap per installed sub-PTE** (`kadd = kpte`): the
"no install without a counted rmap" half of the obligation, made exact. -/
theorem install_balanced_iff (r : Rmap) (hr : r.Balanced) (kadd kpte : Int) :
    (r.install kadd kpte).Balanced ↔ kadd = kpte := by
  simp only [Rmap.Balanced, Rmap.install] at *; omega

/-- **Zap always preserves balance** — it removes exactly the present count: the "no double-remove" half
holds unconditionally (R13's empirical finding that the zap side is correct). -/
theorem zap_preserves (r : Rmap) (hr : r.Balanced) (j : Int) : (r.zap j).Balanced := by
  simp only [Rmap.Balanced, Rmap.zap] at *; omega

/-- **THE BUG — an install UNDER-ADD breaks balance the wrong way**: fewer rmap-adds than sub-PTEs
installed (`kadd < kpte`) leaves `mapcount < present`. -/
theorem underadd_breaks (r : Rmap) (hr : r.Balanced) {kadd kpte : Int} (hunder : kadd < kpte) :
    (r.install kadd kpte).mapcount < (r.install kadd kpte).present := by
  simp only [Rmap.Balanced, Rmap.install] at *; omega

/-- **THE OVER-REMOVE, with NO FREE in the model.** Start from a fresh folio; install `kpte` present
sub-PTEs but issue only `kadd < kpte` rmap-adds; then zap removes the `kpte` present sub-PTEs (correctly,
once each). `mapcount` is driven to `kadd − kpte < 0` — i.e. `_mapcount ≤ -2`, the underflow the probe
caught. The derivation uses no refcount, no lifetime, no free: a deterministic counting imbalance. -/
theorem underadd_zap_underflows {kadd kpte : Int} (hunder : kadd < kpte) :
    ((Rmap.fresh.install kadd kpte).zap kpte).mapcount < 0 := by
  simp only [Rmap.fresh, Rmap.install, Rmap.zap]; omega

/-- **The over-remove is INDEPENDENT OF THE FREE** (R13 verdict 2, formal form). Same statement as
`underadd_zap_underflows`, named to record the point: a folio that is over-removed need NOT be freed
(B2: allocated, refcount 10); a freed one (A2) is an incidental correlate. This is why the ref-free gate
is dead and the lifetime framings (R11/R12) do not bind. -/
theorem overremove_independent_of_free {kadd kpte : Int} (hunder : kadd < kpte) :
    ((Rmap.fresh.install kadd kpte).zap kpte).mapcount < 0 :=
  underadd_zap_underflows hunder

/-! ### Localizing the under-add to the `vsub ≠ psub` batching edge (R13's prime suspect) -/

/-- Shape model of the suspect batched add-count. `pgcl_pte_batch` groups by PHYSICAL sub-index, so the
install issues a counted `folio_add_rmap_pte` for each sub-PTE that sits on the identity diagonal
(`π i = i`) and MISSES the π-displaced ones (`π i ≠ i`) — the `mremap`/`relocate_vma_down` sub-PTEs where
vsub ≠ psub. (A shape model of the *direction* of the miscount; the reproducer pins the exact file:line.) -/
def batchAdd (π : Nat → Nat) (n : Nat) : Nat := (List.range n).countP (fun i => π i == i)

/-- For identity π the physical grouping equals the virtual count — every installed sub-PTE is counted,
balance holds (this is why the un-relocated paths read balanced in R13). -/
theorem batchAdd_identity_4 : batchAdd (fun i => i) 4 = 4 := by decide

/-- **The `migsub` π under-adds by one** over a 4-fragment window — the same `π(2) = 1` witness as
`Permute.migsub_observed_case` (PID1's relocated stack, vsub 2 / psub 1). The physical-grouping batch
counts 3 of the 4 present sub-PTEs, missing the displaced one: `kadd = 3 < 4 = kpte`. -/
theorem migsub_underadds : batchAdd (fun i => if i = 2 then 1 else i) 4 = 3 := by decide

/-- **Capstone — the named π drives the probe's edge with no free.** The migsub under-add (`kadd = 3`)
followed by a correct zap of the 4 present sub-PTEs leaves `mapcount = -1`, i.e. `_mapcount = -2` —
exactly R13's faithful-laptop anchors (pfn 55641, pfn 545d2; `mc = -2`). The whole chain is a counting
imbalance seeded at the `vsub ≠ psub` batching edge; lifetime never appears. -/
theorem migsub_underflow : ((Rmap.fresh.install 3 4).zap 4).mapcount = -1 := by
  simp only [Rmap.fresh, Rmap.install, Rmap.zap]; omega

end Tessera

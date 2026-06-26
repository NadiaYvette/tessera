/-
  Tessera — Layer A / M2: fork / COW-share (proof-obligation categories G + A;
  invariants 6 and 2).  The remaining half of the copy-on-write lifecycle: fork is
  the ENTRY to sharing, `Cow.lean`'s break is the exit.

  When an address space forks, each private *writable* mapping becomes a shared,
  *write-protected* mapping in both parent and child:

    * the backing object gains the child as a sharer (mapcount += 1) — the refcount
      discipline of `Sharing.lean` (category G, invariant 6);
    * the writable mapping is WRITE-PROTECTED in both, so a later write faults and
      triggers COW-break — category A, the telix #10 missing-write-protect bug;
    * the accompanying TLB flush is already discharged as the perm-agreement
      coherence result of `Mprotect.lean` (a flush-less perm downgrade is a provable
      error there), so it is not re-proved here;
    * KERNEL extents must NOT be COW-shared into a child (telix #1): a child user
      address space must never gain a mapping to a kernel backing object.

  The COW correctness invariant made explicit: a *shared* object (≥ 2 sharers) grants
  NO writer.  Fork establishes it; a fork that shares without write-protecting
  violates it (two writers to one object = silent cross-address-space corruption); a
  write must COW-break — recovering a private, again-writable copy — before writing.
-/
import Tessera.Sharing
import Tessera.Cow
import Tessera.Basic

namespace Tessera

/-- A backing object seen through the COW layer: the shared `sites` + cached count
(`Sharing.lean`), the uniform `perm` its current sharers hold (read-only once shared,
until a break), and whether it is a `kernel` extent. -/
structure CowObj (σ : Type) where
  backing : Backing σ
  perm    : Perm
  kernel  : Bool

namespace CowObj

/-- "Shared" = two or more sharers map this object. -/
def Shared {σ : Type} (o : CowObj σ) : Prop := 2 ≤ o.backing.mapcount

/-- **COW well-formedness** (invariant 6): the refcount discipline holds, AND a
shared object is write-protected — no sharer holds write permission while shared.
The second conjunct is what makes COW sound: a write to a shared page cannot silently
leak across address spaces. -/
def WF {σ : Type} (o : CowObj σ) : Prop :=
  o.backing.WF ∧ (o.Shared → o.perm.write = false)

/-- **Fork**: add the child as a sharer (count += 1) and WRITE-PROTECT the mapping
(`write := false`) in both parent and child. -/
def fork {σ : Type} (o : CowObj σ) (child : σ) : CowObj σ :=
  ⟨o.backing.add [child] 1, { o.perm with write := false }, o.kernel⟩

/-- **A buggy fork that shares WITHOUT write-protecting** (telix #10): the child is
added but the writable permission is kept. -/
def forkBuggy {σ : Type} (o : CowObj σ) (child : σ) : CowObj σ :=
  ⟨o.backing.add [child] 1, o.perm, o.kernel⟩

/-- **Fork preserves the COW discipline** (invariant 6 + refcount discipline): the
backing count tracks the new sharer (reusing `add_wf`), and the result is
write-protected, so "shared ⇒ no writer" holds.  Fork ESTABLISHES write-protection
regardless of the parent's prior permission. -/
theorem fork_wf {σ : Type} {o : CowObj σ} (h : o.backing.WF) (child : σ) :
    (o.fork child).WF := by
  refine ⟨?_, ?_⟩
  · exact Backing.add_wf h [child]
  · intro _; rfl

/-- **Fork write-protects** (category A, telix #10): the forked mapping grants no
writer, so a subsequent write faults and must go through COW-break. -/
theorem fork_write_protected {σ : Type} (o : CowObj σ) (child : σ) :
    (o.fork child).perm.write = false := rfl

/-- **Fork shares**: the child becomes a sharer; the count rises by exactly one. -/
theorem fork_mapcount {σ : Type} (o : CowObj σ) (child : σ) :
    (o.fork child).backing.mapcount = o.backing.mapcount + 1 := rfl

/-- **Sharing without write-protecting is a provable error** (telix #10).  From a
private *writable* mapping (one sharer, well-formed), the buggy fork adds the child
but keeps write permission: now two address spaces share one object and BOTH may
write — a write in one silently corrupts the other.  The COW invariant catches it. -/
theorem forkBuggy_breaks_wf :
    ∃ (o : CowObj Nat) (child : Nat),
      o.WF ∧ (o.forkBuggy child).Shared ∧ ¬ (o.forkBuggy child).WF := by
  refine ⟨⟨⟨[0], 1⟩, ⟨true, true, false⟩, false⟩, 1, ?_, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    intro hsh; exfalso
    have : (2 : Nat) ≤ 1 := hsh
    omega
  · show (2 : Nat) ≤ _
    simp only [CowObj.forkBuggy, Backing.add]; omega
  · rintro ⟨-, himp⟩
    have hsh : (CowObj.forkBuggy (⟨⟨[0], 1⟩, ⟨true, true, false⟩, false⟩ : CowObj Nat) 1).Shared := by
      show (2 : Nat) ≤ _
      simp only [CowObj.forkBuggy, Backing.add]; omega
    have hw := himp hsh
    simp [CowObj.forkBuggy] at hw

/-- A child user address space is **safe** only if it shares no kernel object. -/
def UserSafe {σ : Type} (o : CowObj σ) : Prop := o.kernel = false

/-- **Fork preserves user-safety** for a user object: the child gains no kernel
mapping (fork carries the kernel flag unchanged). -/
theorem fork_userSafe {σ : Type} {o : CowObj σ} (h : o.UserSafe) (child : σ) :
    (o.fork child).UserSafe := h

/-- **COW-sharing a kernel extent into a child is a provable error** (telix #1): if
the parent extent is a kernel object, the fork hands the child a mapping to kernel
memory — the child is no longer user-safe.  The guard `o.kernel = false` is necessary;
omitting it is the telix #1 security bug. -/
theorem forkKernel_breaks_userSafe :
    ∃ (o : CowObj Nat) (child : Nat),
      o.kernel = true ∧ ¬ (o.fork child).UserSafe := by
  refine ⟨⟨⟨[0], 1⟩, ⟨true, false, false⟩, true⟩, 1, rfl, ?_⟩
  intro h; simp [CowObj.UserSafe, CowObj.fork] at h

/-- **The COW lifecycle is conservative** (fork then break preserves the count).
Forking a private writable object (one sharer) makes it shared + RO (two sharers);
when the child writes, COW-break splits it back into the still-mapped original (one
sharer) and the child's fresh private writable copy (one sharer) — total count
preserved, the writer private again.  Composes `fork_mapcount` with
`Backing.cow_conserves`. -/
theorem fork_then_cowbreak_conserves {σ : Type} (o : CowObj σ) (child : σ)
    (hm : 1 ≤ o.backing.mapcount) :
    ((o.fork child).backing.cowShared).mapcount + (Backing.cowPriv child).mapcount
      = (o.fork child).backing.mapcount := by
  apply Backing.cow_conserves
  show 1 ≤ o.backing.mapcount + 1
  omega

end CowObj

end Tessera

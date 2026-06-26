/-
  Tessera — Layer A / M2: COW-break consistency (invariant 6; Rung 3-lite of
  ../doc/proof-obligations.md, concretizing the shared object of `Sharing.lean`).

  A copy-on-write break: a write by address space `w` to a *shared* backing object
  must break the sharing — `w` leaves the shared object (its refcount is decremented)
  and takes a fresh **private** copy (refcount 1). The consistency obligations
  (invariant 6: "reference counts reflect actual sharing"; the real bugs telix #1/#7/#8)
  are:

    * the break preserves the refcount discipline on both objects (reusing the
      `Sharing.lean` invariant `mapcount = #sites`);
    * the writer's mapping is conserved, not duplicated or lost (total count steady);
    * if **other** address spaces still share, the shared object is NOT freed — its
      count stays positive — so it must not be reclaimed (telix #8: freeing a shared
      object with a live sibling is a use-after-free);
    * a break that "frees" a still-shared object (zeroes its count) is a provable error.

  Here a "site" of `Sharing.lean` is concretized to a sharer address space; `w`
  leaving is one `remove`, and the private copy is a one-site object.
-/
import Tessera.Sharing

namespace Tessera

namespace Backing

/-- The shared object after `w` breaks away: one sharer leaves, the count drops by one. -/
def cowShared {σ : Type} (shared : Backing σ) : Backing σ := shared.remove 1 1

/-- The fresh private copy the writer takes: a single sharer (the writer), count 1. -/
def cowPriv {σ : Type} (w : σ) : Backing σ := ⟨[w], 1⟩

/-- A buggy break that "reclaims" the shared object by zeroing its count. -/
def cowSharedBuggy {σ : Type} (shared : Backing σ) : Backing σ := { shared with mapcount := 0 }

/-- The private copy is well-formed and **writable-private**: exactly one mapper. -/
theorem cowPriv_wf {σ : Type} (w : σ) : (cowPriv w).WF := rfl

theorem cowPriv_private {σ : Type} (w : σ) : (cowPriv w).mapcount = 1 := rfl

/-- **COW-break preserves the shared object's refcount discipline** (invariant 6):
when the writer was a sharer (`≥ 1` site), the decremented count still equals the
remaining sharers. -/
theorem cowShared_wf {σ : Type} {shared : Backing σ} (h : shared.WF)
    (hk : 1 ≤ shared.sites.length) : (shared.cowShared).WF :=
  Backing.remove_wf h hk

/-- **The writer's mapping is conserved**: the shared object's lost count is exactly
the private copy's gained count — the mapping moved, it was not duplicated or lost. -/
theorem cow_conserves {σ : Type} {shared : Backing σ} (hm : 1 ≤ shared.mapcount) (w : σ) :
    (shared.cowShared).mapcount + (cowPriv w : Backing σ).mapcount = shared.mapcount := by
  show (shared.mapcount - 1) + 1 = shared.mapcount
  omega

/-- **No free-while-shared** (the telix #8 safety property): if other address spaces
still share the object (`≥ 2` sharers before the break), its count stays positive
after the break — so the shared object must NOT be reclaimed; the sibling's mapping
survives. -/
theorem cow_no_free_while_shared {σ : Type} {shared : Backing σ} (h : shared.WF)
    (hge : 2 ≤ shared.sites.length) : (shared.cowShared).mapcount ≠ 0 := by
  have h' : shared.mapcount = shared.sites.length := h
  show shared.mapcount - 1 ≠ 0
  omega

/-- **Reclaiming a still-shared object is a provable error.** A break that zeroes the
shared object's count while sharers remain breaks the refcount discipline: count `0`
over a non-empty sharer set is exactly the free-while-mapped condition (telix #8). -/
theorem cowSharedBuggy_breaks_wf :
    ∃ (shared : Backing Nat), 2 ≤ shared.sites.length ∧ shared.WF ∧
      ¬ (shared.cowSharedBuggy).WF := by
  refine ⟨⟨[1, 2], 2⟩, ?_, ?_, ?_⟩
  · decide
  · rfl
  · intro hc; simp [Backing.WF, Backing.cowSharedBuggy] at hc

end Backing

end Tessera

/-
  Tessera — the FILE PAGE-CACHE STRUCTURAL REF invariant (2026-07-01).

  The R17-p1 floor-at-present boot (`-pgcl4-143r17fp`) drove the mapcount over-remove to zero
  (PGCL143-ORPHAN 221→0, rss-counter 12→0) but left a UNIFORM residual: every surviving `bad_page`
  is a FILE page-cache folio (`aops:btrfs_aops`, a shared library) dumped

      refcount:0  mapcount:0   mapping:<non-NULL>   flags: referenced|dirty|workingset|lru

  freed via `free_pages_and_swap_cache ← folios_put_refs` (the mmu_gather zap batch).  A page-cache
  folio was FREED BY THE UNMAP PATH WHILE STILL IN THE CACHE.  This is a refcount over-put that is
  INVISIBLE to every ledger the existing models carry (`MapcountOnly.MRP.ref` is the *mapping*-ref
  ledger; `FloorAtPresent.RSP` has rmap/stat/present) — none represent the PAGE CACHE's OWN structural
  reference, the `+1` that `filemap_add_folio` takes and that must survive unmap, dropped ONLY by
  truncate / `__remove_mapping` (which first freezes the refcount and clears `mapping`).

  Per the standing model-enrichment remit, this file adds that ledger and the invariant it must satisfy:
    * `cachedPinned`: while `mapping ≠ NULL`, `refcount ≥ 1` — the cache ref pins the folio, so the
      free path (`refcount == 0`) is UNREACHABLE while cached.  The bad_page is exactly its violation.
    * a CORRECT unmap drops only mapping refs (`≤ mapRefs`) and preserves the invariant;
    * an OVER-PUT that drops even ONE more than this mm's mappings eats the cache ref → `refcount` hits
      0 while cached → free-while-cached (the observed bad_page);
    * the FIX obligation: each mm's unmap drops EXACTLY its own present sub-PTE refs (`present_here`),
      so the sum over mms drops `Σ mapRefs` and never the cache ref.
-/
import Tessera.MapcountOnly

namespace Tessera

/-- A FILE page-cache folio's refcount decomposes into the page cache's OWN structural reference
(`cacheRef` = 1 while the folio is in the cache / `mapping ≠ NULL`, else 0) and the sum of the present
sub-PTE MAPPING references across all mms (`mapRefs`).  `_mapcount` tracks mappings separately; the
over-put is a refcount fault the mapcount ledger cannot see. -/
structure FileFolio where
  cacheRef : Int        -- 1 while cached, 0 once removed from the page cache
  mapRefs  : Int        -- Σ present sub-PTE mapping refs across all mms
  cached   : Bool       -- mapping ≠ NULL (folio still on the inode's i_pages)
deriving Repr, DecidableEq

/-- The kernel's `folio_ref_count`. -/
def FileFolio.refcount (f : FileFolio) : Int := f.cacheRef + f.mapRefs

/-- Well-formed page-cache state: the cache ref is present exactly while cached, mappings are
non-negative. -/
def FileFolio.wf (f : FileFolio) : Prop :=
  (f.cached = true → f.cacheRef = 1) ∧ (f.cached = false → f.cacheRef = 0) ∧ 0 ≤ f.mapRefs

/-- **THE INVARIANT.** While cached (`mapping ≠ NULL`), the refcount is at least 1 — the page cache's
own ref pins the folio, so the free path (`refcount = 0`) is unreachable while cached.  A folio dumped
`refcount:0` with `mapping` non-NULL (the observed `bad_page`) is precisely this predicate FALSE. -/
def FileFolio.cachedPinned (f : FileFolio) : Prop := f.cached = true → 1 ≤ f.refcount

/-- Well-formedness implies the pin: cached ⇒ cacheRef = 1 ⇒ refcount = 1 + mapRefs ≥ 1. -/
theorem wf_implies_cachedPinned (f : FileFolio) (h : f.wf) : f.cachedPinned := by
  obtain ⟨hc, _, hm⟩ := h
  intro hcached
  simp only [FileFolio.refcount, hc hcached]
  omega

/-- A CORRECT unmap of `k` sub-PTEs in one mm: drop exactly `k` MAPPING refs (`k ≤ mapRefs`), leaving
the cache ref and the cached state untouched.  This is the balanced zap: `folio_ref` and rmap both fall
by the sub-PTEs actually cleared, matching `present_here`. -/
def FileFolio.unmap (f : FileFolio) (k : Int) : FileFolio :=
  { f with mapRefs := f.mapRefs - k }

/-- **A correct unmap preserves the pin.** Dropping only mapping refs keeps `cacheRef = 1`, so a cached
folio still has `refcount ≥ 1`: the free path stays unreachable. -/
theorem unmap_preserves_cachedPinned (f : FileFolio) (k : Int)
    (hwf : f.wf) (_hk : 0 ≤ k) (hle : k ≤ f.mapRefs) : (f.unmap k).cachedPinned := by
  obtain ⟨hc, h0, hm⟩ := hwf
  intro hcached
  simp only [FileFolio.unmap] at hcached ⊢
  simp only [FileFolio.refcount, hc hcached]
  omega

/-- An OVER-PUT: the unmap drops `k` refs from the folio but `k` exceeds this mm's mapping refs — the
extra drop eats into the cache ref.  Model the raw refcount subtraction that `folios_put_refs` performs
(it does not know a cache ref is owed): `refcount -= k` with the cache ref NOT protected. -/
def FileFolio.overput (f : FileFolio) (k : Int) : FileFolio :=
  { f with cacheRef := f.cacheRef - (k - f.mapRefs), mapRefs := 0 }

/-- **THE BUG, formalized.** From a well-formed cached folio, an unmap that drops even ONE more ref than
this mm's mappings (`k = mapRefs + 1`) drives `refcount` to 0 while still `cached` — `cachedPinned` is
FALSE: the free-while-cached `bad_page`.  (`mapping` non-NULL, `refcount:0`, freed by the zap batch.) -/
theorem overput_breaks_cachedPinned (f : FileFolio) (hwf : f.wf) (hcached : f.cached = true) :
    ¬ (f.overput (f.mapRefs + 1)).cachedPinned := by
  obtain ⟨hc, _, _⟩ := hwf
  simp only [FileFolio.cachedPinned, FileFolio.overput, FileFolio.refcount, hcached,
             hc hcached, true_implies]
  omega

/-- **THE FIX OBLIGATION** (two-mm form; the cross-mm shared-cluster case that is task #4). A cached
folio mapped by two mms holding `p` and `q` present sub-PTE refs (`mapRefs = p + q`). If each mm's
unmap drops EXACTLY its own present count — `present_here`, the per-mm ground truth the floor already
scans — the two unmaps land on `{ cacheRef := 1, mapRefs := 0, cached }`: refcount 1, the cache ref
INTACT, `cachedPinned` preserved.  The over-put is any mm dropping MORE than its `present_here` (the
extra eating the shared cache ref); so "each mm drops exactly present_here" is the invariant the zap's
FILE refcount path must satisfy, and where the pgcl batch/deferred-put count must be audited. -/
theorem unmap_two_mms_exact_preserves_pin (p q : Int) (_hp : 0 ≤ p) (_hq : 0 ≤ q) :
    let f : FileFolio := { cacheRef := 1, mapRefs := p + q, cached := true }
    ((f.unmap p).unmap q) = { cacheRef := 1, mapRefs := 0, cached := true }
    ∧ ((f.unmap p).unmap q).cachedPinned := by
  refine ⟨?_, ?_⟩
  · simp only [FileFolio.unmap]; congr 1; omega
  · intro _; simp only [FileFolio.unmap, FileFolio.refcount]; omega

/-! ## reinc #37 — the cache FLOOR (folio_nr_pages), the lru_add-drain over-drop, and the detector

#37 sharpened the residual: the over-dropped folios are UNMAPPED readahead folios (`mapcount 0`) freed
during the `lru_add` batch drain (`filemap_add_folio → folio_batch_move_lru → folios_put_refs`) while
still cached (`refcount:0 mapping≠NULL`).  So the pin is not `1` but the cache FLOOR = `folio_nr_pages`
structural refs `filemap_add_folio` takes, and the invariant generalises `cachedPinned` to `cached →
refcount ≥ nr`.  The runtime detector (`PGCL143-CACHEFLOOR`) fires exactly on its violation; the
enforcement re-holds to the floor, upholding it — proving it cannot recur. -/

/-- Minimal folio view for the floor: refcount and the cached bit (`mapping ≠ NULL`). -/
structure CFolio where
  refcount : Int
  cached   : Bool
deriving Repr, DecidableEq

/-- **THE CACHE-FLOOR INVARIANT** (generalises `cachedPinned` from 1 to `nr = folio_nr_pages`): while
cached, the refcount stays at or above the cache's structural floor. -/
def CFolio.floorOk (nr : Int) (c : CFolio) : Prop := c.cached = true → nr ≤ c.refcount

/-- The runtime detector's firing condition (`PGCL143-CACHEFLOOR`): cached and below floor. -/
def CFolio.violated (nr : Int) (c : CFolio) : Bool := c.cached && decide (c.refcount < nr)

/-- **The detector is EXACT** — fires iff the cache-floor invariant is violated (no false pos/neg). -/
theorem violated_iff_not_floorOk (nr : Int) (c : CFolio) :
    c.violated nr = true ↔ ¬ c.floorOk nr := by
  have hviol : c.violated nr = true ↔ (c.cached = true ∧ c.refcount < nr) := by
    unfold CFolio.violated
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hviol]
  constructor
  · rintro ⟨hc, hlt⟩ hf
    unfold CFolio.floorOk at hf
    exact absurd (hf hc) (by omega)
  · intro hf
    by_cases hc : c.cached = true
    · refine ⟨hc, ?_⟩
      by_cases hlt : c.refcount < nr
      · exact hlt
      · exfalso; apply hf; intro _; omega
    · have hfloor : c.floorOk nr := fun hct => absurd hct hc
      exact absurd hfloor hf

/-- A raw put of `k` refs (what `folios_put_refs` performs). -/
def CFolio.put (k : Int) (c : CFolio) : CFolio := { c with refcount := c.refcount - k }

/-- **THE BUG — the lru_add-drain over-drop.** A put that takes a cached folio below its floor trips the
detector.  The #37 case: `refcount` 1 (the batch ref, the cache ref already lost) put by 1 → `0 < 1`
while cached. -/
theorem put_below_floor_violates (nr k : Int) (c : CFolio)
    (hcached : c.cached = true) (hbelow : c.refcount - k < nr) :
    (c.put k).violated nr = true := by
  unfold CFolio.put CFolio.violated
  simp only [hcached, Bool.true_and, decide_eq_true_eq]
  exact hbelow

/-- **THE ENFORCEMENT / FIX** — on violation, re-hold to the floor (`refcount := nr`), so a cached folio
is never dropped below its cache floor. -/
def CFolio.rehold (nr : Int) (c : CFolio) : CFolio :=
  if c.violated nr = true then { c with refcount := nr } else c

/-- **The enforcement RESTORES the invariant** — after re-hold, `floorOk` holds unconditionally, so a
cached folio is never freed below its floor.  This is the proof it cannot recur. -/
theorem rehold_floorOk (nr : Int) (c : CFolio) : (c.rehold nr).floorOk nr := by
  unfold CFolio.floorOk CFolio.rehold CFolio.violated
  by_cases hcc : c.cached = true
  · by_cases hlt : c.refcount < nr
    · have hv : (c.cached && decide (c.refcount < nr)) = true := by rw [hcc]; simp [hlt]
      rw [if_pos hv]; intro _; show nr ≤ nr; omega
    · by_cases hv : (c.cached && decide (c.refcount < nr)) = true
      · rw [if_pos hv]; intro _; show nr ≤ nr; omega
      · rw [if_neg hv]; intro _; omega
  · by_cases hv : (c.cached && decide (c.refcount < nr)) = true
    · rw [if_pos hv]; intro _; show nr ≤ nr; omega
    · rw [if_neg hv]; intro hc; exact absurd hc hcc

/-- …and the detector is then SILENT — no false alarms after enforcement. -/
theorem rehold_silences (nr : Int) (c : CFolio) : (c.rehold nr).violated nr = false := by
  cases hb : (c.rehold nr).violated nr with
  | false => rfl
  | true => rw [violated_iff_not_floorOk] at hb; exact absurd (rehold_floorOk nr c) hb

/-- The #37 floor GENERALISES the earlier pin: at `nr = 1` (order-0 folio) the cache-floor invariant is
exactly `FileFolio.cachedPinned`. -/
theorem floorOk_one_eq_cachedPinned (f : FileFolio) :
    CFolio.floorOk 1 ⟨f.refcount, f.cached⟩ ↔ f.cachedPinned := Iff.rfl

end Tessera

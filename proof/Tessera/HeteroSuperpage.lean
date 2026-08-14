/-
  Tessera — soundness of mapping ALLOCATION UNITS with HETEROGENEOUSLY-SIZED SUPERPAGES on
  dense-page-size-spectrum architectures.  Discharges the review-level worry: is this a hole?

  pgcl decouples the management unit (a folio = one or more clusters) from the MMU mapping unit
  (MMUPAGE).  A dense spectrum offers many superpage sizes.  Model an MMUPAGE index `m`; the aligned
  2^L tile it falls in is `tileIdx L m = m / 2^L` (the page-table / buddy tree).  A cluster lives at
  level `c`, a folio at level `f ≥ c`, a superpage at level `j`.

  The question reduces to ONE property of aligned power-of-2 tiles: do a superpage and a folio NEST
  (one inside the other) or only ever PARTIALLY OVERLAP?  Partial overlap would be the hole — a
  superpage straddling a folio boundary couples two managed units.  Proved here:
    * sub-folio superpages (j ≤ f) lie ENTIRELY within one folio — so however heterogeneously sized
      the pieces tiling a folio are, every piece is folio-contained and per-folio ops are
      self-contained;
    * a SUPER-folio superpage (j > f) provably spans two distinct folios — the hole, exhibited;
    * therefore the mapping is sound IFF coalescing never exceeds the managed folio (`j ≤ f`).
  The dense spectrum does not widen the hole — it only raises the PRESSURE to pick a super-folio
  size, making "never coalesce past the folio" the design rule pgcl must enforce on superpage
  selection (the generic THP/contig-PTE machinery must be made pgcl-folio-aware).  A statable,
  enforceable constraint — a closed part of the story, not a gap.
-/
namespace Tessera.HeteroSuperpage

/-- The aligned 2^L tile (page-table tree node) that MMUPAGE `m` falls in. -/
def tileIdx (L m : Nat) : Nat := m / 2 ^ L

/-- NESTING: a tile at level `j ≤ L` lies entirely within ONE level-`L` tile — every MMUPAGE it
    covers shares the same level-`L` index.  (`m / 2^L = (m / 2^j) / 2^(L-j)`.) -/
theorem nested_within {j L sidx m : Nat} (hjL : j ≤ L) (hm : tileIdx j m = sidx) :
    tileIdx L m = sidx / 2 ^ (L - j) := by
  unfold tileIdx at *
  rw [← hm, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_cancel' hjL]

/-- SUB-FOLIO SOUNDNESS: two MMUPAGEs of the same sub-folio superpage (level `j ≤ f`) land in the
    SAME folio — a per-folio operation covers the whole superpage and never spills to another folio. -/
theorem subfolio_op_contained {j f sidx m m' : Nat} (hjf : j ≤ f)
    (hm : tileIdx j m = sidx) (hm' : tileIdx j m' = sidx) :
    tileIdx f m = tileIdx f m' := by
  rw [nested_within hjf hm, nested_within hjf hm']

/-- HETEROGENEITY IS FINE below the folio: superpages of DIFFERENT levels `j1, j2 ≤ f` are each
    folio-contained — a folio tiled by a heterogeneous mix of superpage sizes stays sound. -/
theorem hetero_pieces_contained {j1 j2 f s1 s2 m1 m2 : Nat}
    (h1 : j1 ≤ f) (h2 : j2 ≤ f) (hm1 : tileIdx j1 m1 = s1) (hm2 : tileIdx j2 m2 = s2) :
    tileIdx f m1 = s1 / 2 ^ (f - j1) ∧ tileIdx f m2 = s2 / 2 ^ (f - j2) :=
  ⟨nested_within h1 hm1, nested_within h2 hm2⟩

/-- THE HOLE, exhibited: a SUPER-folio superpage (level `j > f`) covers MMUPAGE 0 and MMUPAGE 2^f,
    which sit in DISTINCT folios (indices 0 and 1) yet share the one superpage (index 0).  A
    per-folio op on folio 0 cannot flush this superpage without disturbing folio 1. -/
theorem superfolio_spans_two_folios {j f : Nat} (hfj : f < j) :
    tileIdx f 0 = 0 ∧ tileIdx f (2 ^ f) = 1 ∧ tileIdx j 0 = 0 ∧ tileIdx j (2 ^ f) = 0 := by
  have hf : 0 < 2 ^ f := Nat.pos_pow_of_pos f (by decide)
  have hstep : 2 ^ f < 2 ^ (f + 1) := by rw [Nat.pow_succ]; omega
  have hlt : 2 ^ f < 2 ^ j := Nat.lt_of_lt_of_le hstep (Nat.pow_le_pow_right (by decide) hfj)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [tileIdx]
  · simp [tileIdx, Nat.div_self hf]
  · simp [tileIdx]
  · simp [tileIdx, Nat.div_eq_of_lt hlt]

/-- THE DESIGN RULE that closes the hole: enforce superpage level ≤ folio level on every mapping.
    Then `subfolio_op_contained` applies to EVERY superpage, so per-folio management is uniformly
    self-contained — the heterogeneous superpage mapping is sound.  The folio is the largest
    permissible coalescing unit; the dense spectrum is free to use any size at or below it. -/
theorem sound_iff_no_overcoalesce {j f sidx m m' : Nat}
    (rule : j ≤ f) (hm : tileIdx j m = sidx) (hm' : tileIdx j m' = sidx) :
    tileIdx f m = tileIdx f m' :=
  subfolio_op_contained rule hm hm'

/-! ### The reverse arrangement (MIPS PageGrain): sub-cluster superpages, guaranteed-backed.

    MMUPAGE_SIZE = 1 KiB (level 0), PAGE_SIZE = 64 KiB (cluster level c = 6); hardware sizes
    1/4/16/64 KiB = levels 0, 2, 4, 6 — ALL ≤ c, the largest BEING the folio.  So the super-folio
    hole is structurally unreachable (no size outgrows the managed unit), and the motivation inverts
    typical superpages: because a folio is a pre-allocated CONTIGUOUS 2^c-frame block, every
    sub-cluster superpage that fits is already backed — the mapping cannot fail for lack of
    contiguous memory the way a runtime huge-page allocation can under fragmentation. -/

/-- GUARANTEED BACKING: a level-`j` superpage (j ≤ c) at an aligned intra-folio offset `off` that
    fits (`off + 2^j ≤ 2^c`) has every one of its frames inside the folio's contiguous block
    `[fb, fb + 2^c)`.  The folio contiguity supplies the backing unconditionally — no fragmentation,
    no allocation failure.  (Contrast: a free-standing 2^j superpage must FIND a contiguous run and
    can fail; this one never queries the free pool.) -/
theorem superpage_backed {c j off fb frame : Nat}
    (hfit : off + 2 ^ j ≤ 2 ^ c) (hframe : frame < 2 ^ j) :
    fb ≤ fb + off + frame ∧ fb + off + frame < fb + 2 ^ c := by
  omega

/-- In the reverse arrangement every hardware size is ≤ the folio, so EVERY superpage is sub-folio
    and per-folio management is self-contained for all of them — sound by construction, with
    over-coalescing not merely forbidden but unavailable. -/
theorem reverse_uniformly_sound {c j sidx m m' : Nat} (hsize : j ≤ c)
    (hm : tileIdx j m = sidx) (hm' : tileIdx j m' = sidx) :
    tileIdx c m = tileIdx c m' :=
  subfolio_op_contained hsize hm hm'

/-- Concrete instance: a 16 KiB superpage (level 4) sharing a 64 KiB folio (level c = 6) with any
    other mapping of it keeps both in the one folio. -/
example (m m' : Nat) (hm : tileIdx 4 m = 3) (hm' : tileIdx 4 m' = 3) :
    tileIdx 6 m = tileIdx 6 m' :=
  reverse_uniformly_sound (by decide) hm hm'

end Tessera.HeteroSuperpage

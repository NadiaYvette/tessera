/-
  Tessera — GATHER-LEDGER: the pgcl deferred-FREE phantom (#143's reincarnation UAF, pinned on the
  laptop 2026-07-01) and the per-sub-PTE genuine-ref FIX (Route 2), stated as a CODE SPEC.

  What the incarnation-stamp detector pinned on the laptop (1840 fires, PGCL143-REINCARN): the bug is
  NOT the mapcount (the floor works; R17's "undercount" was a measured-pre-clear artifact). It is a
  DEFERRED-FREE phantom, the `Deferred.lean` family-(A) hazard in its sharpest pgcl form:

    * The zap batches a cluster's sub-PTEs and DEFERS the free to tlb flush: `zap_present_ptes ->
      __tlb_remove_folio_pages(tlb, page, nr, false)` records `nr` (c01720e "defer all nr refs, no
      eager folio_ref_sub"); at flush `free_pages_and_swap_cache` reads the encoded `nr` and drops
      `nr` refs.  So the gather OWES `nr` free-refs across the window — `owed = nr`.
    * The comment claims "holding all nr refs keeps refcount > 0 until tlb_finish_mmu."  Empirically it
      does NOT: the folio's real refcount is LOWER than `nr` — a PHANTOM.  Three concurrent freers
      (pinned by the detector) then drive it to 0 before the flush: LRU batch drain
      (`folio_batch_move_lru`, ~1000/dominant), COW old-folio put (`wp_page_copy`, ~274), shmem/tmpfs
      eviction (`shmem_undo_range <- __fput`, ~40 — the tmpfs insight, vindicated).  Page freed +
      reused -> the flush's deferred `nr`-drop lands on the next INCARNATION -> `bad_page`.

  This file models that precisely and — per the standing model-enrichment cue — states WHAT THE FIX
  CODE MUST DO, as invariants each kernel site is checked against:

    refcount SPLITS by origin.  `base`   = non-mapping refs (allocation / LRU-isolation / page-cache) —
                                           exactly what the three racers drop.
                                `genuine` = mapping refs ACTUALLY taken (one real `folio_get` per
                                           sub-PTE that installed a present PTE).
    The folio refcount the kernel sees is `refs = base + genuine`.

  THE FIX (Route 2): every ADD site installs ONE genuine ref per new present sub-PTE, every unmap drops
  ONE — so `genuine` tracks the present-set EXACTLY (`Counters.RefTracksPresent`, the per-sub-PTE
  `refcount` discipline of `Counters.lean`).  Then the gather's `owed = nr = (sub-PTEs it cleared) <=
  mapped = genuine <= refs`: the deferred free is `Deferred.Pinned` BY CONSTRUCTION.  Dropping the
  ENTIRE base (every racer at once) still leaves `refs = mapped >= nr > 0` — the folio is live for the
  whole flush window, and by `Incarnation.pinned_inc_correct` it cannot reincarnate.  The UAF is
  structurally impossible.  The phantom (`genuine < mapped`) is the negation, and it reincarnates.

  This is the spec each kernel site must match; §"FIX-CODE OBLIGATIONS" below maps every site to the
  invariant it must preserve.
-/
import Tessera.Incarnation
import Tessera.Counters

namespace Tessera
namespace GatherLedger

open Deferred

/-- A cluster-folio's reference ledger, SPLIT BY ORIGIN.  `base` = non-mapping refs (allocation /
LRU-isolation / page-cache — the refs the three racers drop); `genuine` = mapping refs ACTUALLY taken
(one real `folio_get` per present sub-PTE); `mapped` = live sub-PTE mappings across ALL mms (ground
truth).  The kernel's folio refcount is `refs = base + genuine`. -/
structure Folio where
  base    : Int
  genuine : Int
  mapped  : Int
deriving Repr

/-- The refcount the kernel reads: mapping refs plus the base (LRU/page-cache/alloc) ref. -/
def Folio.refs (f : Folio) : Int := f.base + f.genuine

/-- **THE FIX INVARIANT (Route 2).**  Every live mapping is backed by exactly one genuine ref: the
per-sub-PTE `folio_get`/`folio_put` discipline, read at the folio level.  `genuine = mapped`. -/
def Folio.Genuine (f : Folio) : Prop := f.genuine = f.mapped

/-- **THE PHANTOM (the bug).**  Some mappings never took a genuine ref, so the folio holds FEWER
mapping refs than it has live mappings.  The deferred free will owe more than the folio genuinely
holds. -/
def Folio.Phantom (f : Folio) : Prop := f.genuine < f.mapped

/-- The zap of one batch clears `d` sub-PTEs of ONE mm and DEFERS a free of `d` refs to tlb flush
(`__tlb_remove_folio_pages(.., nr=d)` -> `free_pages_and_swap_cache` drops `d`).  The deferred-free
window is `⟨refs, d⟩`: `d` free-refs owed against `refs` currently held.  A single mm's cleared set
never exceeds the folio's total live mappings, so callers supply `d ≤ mapped`. -/
def Folio.zapWindow (f : Folio) (d : Nat) : Window := ⟨f.refs, d⟩

/-! ## The fix is sound — genuine refs PIN the deferred free -/

/-- **FIX SOUND.**  Under `Genuine`, a zap deferring `d ≤ mapped` free-refs is `Deferred.Pinned`
(`d ≤ refs`): the `d` refs it defers are exactly `d` of the genuine mapping refs the folio still holds
(plus a non-negative base).  So by `Deferred.pinned_live` the folio is LIVE for the whole flush
window. -/
theorem fix_zap_pinned (f : Folio) (d : Nat) (hb : 0 ≤ f.base)
    (hg : f.Genuine) (hd : (d : Int) ≤ f.mapped) : (f.zapWindow d).Pinned := by
  simp only [Folio.Genuine] at hg
  simp only [Folio.zapWindow, Window.Pinned, Folio.refs]
  omega

/-- **FIX vs THE THREE RACERS.**  The freers pinned on the laptop — LRU batch drain, COW old-folio
put, shmem/tmpfs eviction — drop the folio's NON-mapping refs (the `base`).  Under `Genuine`, dropping
the ENTIRE base at once still leaves `refs = mapped ≥ d > 0`: the folio stays LIVE for the deferred
free.  No racer can free it while the flush is owed — the reincarnation is structurally impossible. -/
theorem fix_survives_base_drop (f : Folio) (d : Nat) (hb : 0 ≤ f.base)
    (hg : f.Genuine) (hd : (d : Int) ≤ f.mapped) (hpos : 0 < d) :
    ((f.zapWindow d).drop f.base.toNat).live := by
  simp only [Folio.Genuine] at hg
  simp only [Folio.zapWindow, Window.drop, Window.live, Folio.refs]
  omega

/-! ## The phantom — and only the phantom — reincarnates -/

/-- **THE PHANTOM REINCARNATES.**  Base already drained (`base = 0`, folio off-LRU / uncached — the
common late-teardown state) and a mapping skipped its genuine ref (`genuine < d`, the deferred count).
Then the deferred free owes `d` but the folio holds only `genuine < d` refs: a concurrent freer
dropping the remaining `genuine` reaches `refs = 0` WHILE the free is still owed.  This is exactly
`Deferred.unpinned_freed_while_owed` — the frame is freed and reusable with maintenance still
scheduled against it. -/
theorem phantom_freed_while_owed (f : Folio) (d : Nat) (hbase : f.base = 0)
    (hg : 0 ≤ f.genuine) (hd : f.genuine < (d : Int)) :
    ¬ ((f.zapWindow d).drop (f.zapWindow d).refs.toNat).live
      ∧ 0 < ((f.zapWindow d).drop (f.zapWindow d).refs.toNat).owed := by
  have hrefs : 0 ≤ (f.zapWindow d).refs := by
    simp only [Folio.zapWindow, Folio.refs, hbase]; omega
  have hunpin : (f.zapWindow d).refs < (f.zapWindow d).owed := by
    simp only [Folio.zapWindow, Folio.refs, hbase]; omega
  exact unpinned_freed_while_owed (f.zapWindow d) hrefs hunpin

/-- …and the deferred free, running on the freed (reincarnated) frame, drives the refcount NEGATIVE —
the `bad_page` / `refcount:-N` the laptop dumped.  A consequence of the phantom via
`Deferred.run_on_freed_over_decrements`. -/
theorem phantom_run_underflows (f : Folio) (d : Nat) (hbase : f.base = 0)
    (hg : 0 ≤ f.genuine) (hd : f.genuine < (d : Int)) :
    (((f.zapWindow d).drop (f.zapWindow d).refs.toNat).run).refs < 0 := by
  apply run_on_freed_over_decrements
  · simp only [Window.drop, Folio.zapWindow, Folio.refs, hbase]; omega
  · simp only [Window.drop, Folio.zapWindow]; omega

/-! ## The two failure modes the audit checks for — both land in `Phantom`

A site breaks `RefTracksPresent` in one of two ways; each yields `Phantom`, so the static ref-balance
audit is a search for EITHER — a put that drops more refs than sub-PTEs it clears, or an add that takes
fewer refs than sub-PTEs it installs. -/

/-- A put/unmap that clears `j` sub-PTEs but drops `k` refs. -/
def Folio.putkj (f : Folio) (j k : Int) : Folio :=
  { f with genuine := f.genuine - k, mapped := f.mapped - j }

/-- An add/map that installs `j` sub-PTEs but takes `k` refs. -/
def Folio.addkj (f : Folio) (j k : Int) : Folio :=
  { f with genuine := f.genuine + k, mapped := f.mapped + j }

/-- **OVER-PUT ⟹ phantom** (task #4 "cross-mm shared-cluster over-put"): from `Genuine`, dropping MORE
refs than sub-PTEs cleared (`k > j`) leaves `genuine < mapped`.  This is the laptop's likely site: the
racers (COW put, shmem eviction) are put paths. -/
theorem overput_creates_phantom (f : Folio) (j k : Int) (hg : f.Genuine) (hlt : j < k) :
    (f.putkj j k).Phantom := by
  simp only [Folio.Genuine] at hg
  simp only [Folio.Phantom, Folio.putkj]; omega

/-- **UNDER-ADD ⟹ phantom** (the R11 "double-add" dual — a map taking too few refs): from `Genuine`,
installing MORE sub-PTEs than refs taken (`k < j`) leaves `genuine < mapped`. -/
theorem underadd_creates_phantom (f : Folio) (j k : Int) (hg : f.Genuine) (hlt : k < j) :
    (f.addkj j k).Phantom := by
  simp only [Folio.Genuine] at hg
  simp only [Folio.Phantom, Folio.addkj]; omega

/-- **BALANCED (`k = j`, `RefTracksPresent`) preserves `Genuine`** — the fix, at each site: move refs
and mappings by the SAME amount.  Both directions. -/
theorem balanced_put_preserves_genuine (f : Folio) (j : Int) (hg : f.Genuine) :
    (f.putkj j j).Genuine := by
  simp only [Folio.Genuine] at hg ⊢; simp only [Folio.putkj]; omega

theorem balanced_add_preserves_genuine (f : Folio) (j : Int) (hg : f.Genuine) :
    (f.addkj j j).Genuine := by
  simp only [Folio.Genuine] at hg ⊢; simp only [Folio.addkj]; omega

/-! ## The fix is the `Counters` per-sub-PTE discipline, composed across mms

`Counters.RefTracksPresent` (this mm keeps `refcount = present`) is the per-mm form of the fix.  It is
preserved by the counter ops with a one-line proof each — mirroring what every kernel ADD/REMOVE site
must do: move `refcount` in lockstep with the present-set, per sub-PTE. -/

/-- The per-mm fix discipline: this mm's genuine mapping refs equal its present set. -/
def _root_.Tessera.Counters.RefTracksPresent (c : Counters) : Prop := c.refcount = c.present

/-- **ADD preserves it** — `addk` moves `refcount` and `present` by the same `k` (per-sub-PTE). -/
theorem addk_preserves_refTracks (c : Counters) (k : Int) (h : c.RefTracksPresent) :
    (c.addk k).RefTracksPresent := by
  simp only [Counters.RefTracksPresent, Counters.addk] at *; omega

/-- **REMOVE preserves it** — `remk` moves both by the same `k`. -/
theorem remk_preserves_refTracks (c : Counters) (k : Int) (h : c.RefTracksPresent) :
    (c.remk k).RefTracksPresent := by
  simp only [Counters.RefTracksPresent, Counters.remk] at *; omega

/-- A folio built from TWO mms sharing the cluster (the sharing case that bites), plus a base ref. -/
def folioOf (c1 c2 : Counters) (base : Int) : Folio :=
  ⟨base, c1.refcount + c2.refcount, c1.present + c2.present⟩

/-- **Per-mm discipline ⟹ folio-level `Genuine`.**  If every mm keeps `refcount = present`, the
folio's genuine mapping refs equal its total mapped set. -/
theorem folioOf_genuine (c1 c2 : Counters) (base : Int)
    (h1 : c1.RefTracksPresent) (h2 : c2.RefTracksPresent) :
    (folioOf c1 c2 base).Genuine := by
  simp only [Counters.RefTracksPresent] at h1 h2
  simp only [Folio.Genuine, folioOf]; omega

/-! ## The end-to-end fix theorem -/

/-- **ROUTE 2 CLOSES #143.**  Two mms share a cluster; each keeps the per-sub-PTE ref discipline.
Then any zap deferring `d ≤ mapped` free-refs is `Pinned` — so by `Deferred.pinned_live` the folio is
live for the whole flush window, and no racer frees it. -/
theorem fix_closes_143 (c1 c2 : Counters) (base : Int) (d : Nat)
    (hbase : 0 ≤ base) (h1 : c1.RefTracksPresent) (h2 : c2.RefTracksPresent)
    (hd : (d : Int) ≤ (folioOf c1 c2 base).mapped) :
    ((folioOf c1 c2 base).zapWindow d).Pinned :=
  fix_zap_pinned _ d hbase (folioOf_genuine c1 c2 base h1 h2) hd

/-- …and therefore INCARNATION-CORRECT: the frame the deferred free targets cannot reincarnate.  The
capstone — the per-sub-PTE ref discipline of `Counters` discharges the `Incarnation` obligation, so
the reincarnation UAF pinned on the laptop is ruled out for all interleavings. -/
theorem fix_no_reincarnation (c1 c2 : Counters) (base : Int) (d : Nat) (e : Nat) (p : Pfn)
    (hbase : 0 ≤ base) (h1 : c1.RefTracksPresent) (h2 : c2.RefTracksPresent)
    (hd0 : 0 < d) (hd : (d : Int) ≤ (folioOf c1 c2 base).mapped)
    (hpref : p.refs = ((folioOf c1 c2 base).zapWindow d).refs) (he : p.inc = e) :
    IncCorrect p e ∧ ¬ CanReincarnate p :=
  pinned_inc_correct ((folioOf c1 c2 base).zapWindow d) p e hpref he
    (fix_closes_143 c1 c2 base d hbase h1 h2 hd) hd0

/-! ## FIX-CODE OBLIGATIONS — what each kernel site must do (the spec, mechanized above)

The single obligation is `RefTracksPresent` at every mm: `refcount` moves in lockstep with the
present-set, per sub-PTE.  Concretely, per site (`mm/memory.c`, `mm/rmap.c`):

  * do_anonymous_page  — install `rss` present sub-PTEs, take `rss` genuine refs.  ALREADY CLEAN:
      `if (rss > 1) folio_ref_add(folio, rss - 1)` atop the birth ref  ⟹ `addk rss` (audited).
  * copy_present_ptes (fork) — child gains `nr` present sub-PTEs, take `nr` refs:
      `folio_ref_add(folio, nr)` + `folio_try_dup_anon_rmap_ptes(.., nr, ..)`  ⟹ `addk nr` in the
      child mm.  The pgcl-anon batch path must add exactly `nr`, never fewer (the cross-mm suspect).
  * set_pte_range / filemap / swap-in — `folio_ref_add(folio, nr_ptes - 1)` atop the one held ref
      ⟹ `addk nr_ptes`.
  * zap_present_ptes — clear `nr` present sub-PTEs, DEFER exactly `nr` (`owed = nr`), never more than
      the batch actually cleared: `__tlb_remove_folio_pages(tlb, page, nr, false)`  ⟹ `remk nr` whose
      refs land at flush.  `d ≤ mapped` is precisely "defer no more than you cleared."
  * free_pages_and_swap_cache — at flush drop exactly the encoded `nr`  ⟹ the `remk nr` refs.
  * base ref (LRU-isolation / page-cache / alloc) is SEPARATE from `genuine`; the racers drop only it.
      `fix_survives_base_drop` is why that is safe once `genuine = mapped`.

`addk_preserves_refTracks` / `remk_preserves_refTracks` are the per-site proof obligations: each is
discharged by "this site moves `refcount` by the same `k` as `present`."  Any site that adds fewer
refs than present sub-PTEs (or defers more than it cleared) breaks `RefTracksPresent`, yielding
`Phantom`, yielding `phantom_freed_while_owed` — the exact laptop UAF.  That is the invariant the
static ref-balance audit checks each site against. -/

/-! ## Why the REINCARN detector LIES — a faithful vs a stamp-until-freed detector

The runtime REINCARN check stamps `gather_owes[pfn]` at every defer and clears it only at free
(`mmu_gather.c:210` / `page_alloc.c:3037`), firing on `freed ∧ stamped`.  But `stamped` conflates "a
gather deferred this" with "a gather STILL owes it": once the gather DISCHARGES (its flush drops the
deferred ref) the owe is gone, yet the stamp lingers until the pfn is actually freed.  A later
LEGITIMATE free then fires it — the artifact behind the ~1840 fires with 0–1 real `bad_page`.  The
faithful detector tracks the OUTSTANDING owe (inc at defer, DEC at discharge) and fires on `freed ∧
owed>0`.  Mirrors `Incarnation.probe_faithful` (the correct probe), for the gather-owes detector. -/

/-- Detector state over the event stream. `owed` = undischarged deferred refs; `stamped` = a gather
deferred this pfn since the last free. -/
structure Det where
  owed    : Nat
  stamped : Bool
deriving Repr, DecidableEq

/-- A gather defers a free: owe one more, set the stamp. -/
def Det.defer (d : Det) : Det := { owed := d.owed + 1, stamped := true }

/-- The gather DISCHARGES at flush: it drops one deferred ref.  The buggy detector does NOT clear the
stamp here (only at free) — that is the artifact. -/
def Det.discharge (d : Det) : Det := { d with owed := d.owed - 1 }

/-- **REAL reincarnation** = the pfn is freed while an owe is still OUTSTANDING. -/
def reincarnated (d : Det) : Prop := 0 < d.owed

/-- The REINCARN detector's firing condition at a (non-gather) free. -/
def stampFires (d : Det) : Bool := d.stamped

/-- The faithful detector's firing condition. -/
def faithFires (d : Det) : Bool := decide (0 < d.owed)

/-- **The faithful detector is EXACT** — fires iff a real reincarnation. -/
theorem faith_faithful (d : Det) : faithFires d = true ↔ reincarnated d := by
  simp only [faithFires, reincarnated, decide_eq_true_eq]

/-- **THE ARTIFACT — the stamp detector fires with NO outstanding owe.** After `defer` then `discharge`
the owe is 0 (nothing owed) but the stamp is still set, so a legitimate later free fires it: a FALSE
positive.  This is the ~1840 fires (shared/cached cluster deferred, gather flushed, then freed by LRU
drain / shmem eviction). -/
theorem stamp_false_positive :
    stampFires (Det.discharge (Det.defer ⟨0, false⟩)) = true
    ∧ faithFires (Det.discharge (Det.defer ⟨0, false⟩)) = false := by decide

/-- **THE DETECTOR FIX — clear the stamp when the gather DISCHARGES** (in the `in_gflush` window at
`free_pages_and_swap_cache`), not only at free.  Then no outstanding owe ⟹ no stamp ⟹ no false fire. -/
def Det.dischargeFix (d : Det) : Det :=
  { owed := d.owed - 1, stamped := if d.owed - 1 = 0 then false else d.stamped }

/-- With the fix, the same `defer`→`discharge` sequence leaves the stamp CLEAR — the false positive is
gone. -/
theorem dischargeFix_no_false_positive :
    stampFires (Det.dischargeFix (Det.defer ⟨0, false⟩)) = false := by decide

/-- …and the fix keeps the detector FAITHFUL where it must fire: a genuine reincarnation (freed while
`owed>0`, i.e. the gather has NOT discharged) still trips both `stampFires` and `faithFires`. -/
theorem defer_then_free_still_fires :
    stampFires (Det.defer ⟨0, false⟩) = true ∧ faithFires (Det.defer ⟨0, false⟩) = true := by decide

/-! ## The count-correct per-gather PIN — a ROBUST fix, no `genuine = mapped` needed

`Genuine` above is the IDEAL, but it is FRAGILE: it must hold at EVERY map/unmap site, and the laptop's
residual (r2diag2, 2026-07-02: 68 `folios_put_refs` DOUBLE-puts on shared page-cache clusters, `int3`
in `libcef.so`) shows a phantom the static ref-balance audit still missed.  The PIN is a stronger LOCAL
fix: at `__tlb_remove_folio_pages` the gather takes its OWN dedicated ref (`folio_get`), dropped at its
discharge.  Then `owing ≤ refs` BY CONSTRUCTION — premature free is impossible regardless of the
map-side balance, and the multi-mm shared cluster (which broke the boolean `in_gflush` gate — per-cpu,
unreliable under PREEMPT — and the count gate — re-hold-at-0 race) is handled because each gather's pin
is INDEPENDENT and untouchable by any other path. -/

/-- A cluster's DEFERRED-FREE ledger: `refs` = folio refcount; `owing` = the number of mmu_gathers that
currently owe a discharge, EACH backed by its own dedicated pin (a `folio_get` taken at defer). -/
structure Ledger where
  refs  : Nat
  owing : Nat
deriving Repr, DecidableEq

/-- **THE PIN INVARIANT.**  Every owing gather holds ≥1 dedicated ref, so `owing ≤ refs`.  This is the
deferred put "genuinely pinned" as a COUNT — NOT derived from the fragile `genuine = mapped`. -/
def Ledger.ok (s : Ledger) : Prop := s.owing ≤ s.refs

/-- freed = the refcount reached 0 (the page goes to the buddy / pcp freelist). -/
def Ledger.freed (s : Ledger) : Prop := s.refs = 0

/-- A gather defers a put and TAKES ITS PIN (`folio_get` at `__tlb_remove_folio_pages`): +1 ref, +1 owing. -/
def Ledger.defer (s : Ledger) : Ledger := ⟨s.refs + 1, s.owing + 1⟩

/-- The owing gather DISCHARGES (`free_pages_and_swap_cache` drops its pin): −1 ref, −1 owing. -/
def Ledger.discharge (s : Ledger) : Ledger := ⟨s.refs - 1, s.owing - 1⟩

/-- A non-gather racer (LRU-drain / COW put / shmem eviction) drops ONE non-pin ref.  Sound only when
`owing < refs` — the pins are the gathers' own, untouchable by a racer. -/
def Ledger.racer (s : Ledger) : Ledger := ⟨s.refs - 1, s.owing⟩

theorem Ledger.defer_ok (s : Ledger) (h : s.ok) : (s.defer).ok := by
  simp only [Ledger.ok, Ledger.defer] at *; omega

theorem Ledger.discharge_ok (s : Ledger) (h : s.ok) (ho : 0 < s.owing) : (s.discharge).ok := by
  simp only [Ledger.ok, Ledger.discharge] at *; omega

theorem Ledger.racer_ok (s : Ledger) (h : s.ok) (hr : s.owing < s.refs) : (s.racer).ok := by
  simp only [Ledger.ok, Ledger.racer] at *; omega

/-- **NO PREMATURE FREE (the reincarnation is impossible).**  While any gather owes a deferred put, the
cluster is NOT freed — straight from the invariant.  This is the #143 int3 root ruled out by
construction. -/
theorem Ledger.owing_not_freed (s : Ledger) (h : s.ok) (ho : 0 < s.owing) : ¬ s.freed := by
  simp only [Ledger.ok, Ledger.freed] at *; omega

/-- **THE RACER CANNOT FREE AN OWED CLUSTER.**  A sound racer drop never frees while a gather owes — the
exact fix for the `lru_add_drain` / cross-mm freers the DOUBLEDROP probe pinned on the laptop. -/
theorem Ledger.racer_cannot_free (s : Ledger) (h : s.ok) (ho : 0 < s.owing) (hr : s.owing < s.refs) :
    ¬ (s.racer).freed := by
  simp only [Ledger.ok, Ledger.freed, Ledger.racer] at *; omega

/-- **CROSS-GATHER — the case that broke every gate.**  Two mms' gathers each pin the shared cluster
(`⟨2,2⟩`, all base refs already dropped): the FIRST discharge does NOT free it (the other's pin holds),
the SECOND frees it exactly once, nothing left owing.  No premature free, no double free — by
construction, with no `in_gflush` disambiguation and no re-hold. -/
theorem Ledger.two_gathers_exactly_once :
    ¬ (Ledger.discharge ⟨2, 2⟩).freed
    ∧ (Ledger.discharge (Ledger.discharge ⟨2, 2⟩)).freed
    ∧ (Ledger.discharge (Ledger.discharge ⟨2, 2⟩)).owing = 0 := by
  simp [Ledger.discharge, Ledger.freed]

/-- **NO LEAK.**  The last owner's discharge of a pin-only cluster frees it exactly once. -/
theorem Ledger.last_discharge_frees_once :
    (Ledger.discharge ⟨1, 1⟩).freed ∧ (Ledger.discharge ⟨1, 1⟩).owing = 0 := by
  simp [Ledger.discharge, Ledger.freed]

/-! ### Contrast — the NO-PIN design + the refcount FLOOR band-aid MANUFACTURE the double-free

Without the pin the deferred put leaves the mapping ref merely "in flight": `owing` is NOT backed by a
dedicated ref, so `owing` can exceed `refs`.  A racer then frees the owed cluster, and the refcount
FLOOR band-aid (`folios_put_refs`: `new = k ≤ old ? old−k : 0`) clamps the gather's later STALE put to 0
and the free path re-reads "refs reached 0" → frees it AGAIN: the 68 `folios_put_refs` double-puts. -/

/-- No-pin defer: owe a discharge WITHOUT taking a dedicated ref (the current kernel). -/
def Ledger.deferNoPin (s : Ledger) : Ledger := ⟨s.refs, s.owing + 1⟩

/-- **THE BUG.**  A no-pin defer of a singly-held cluster, then a racer drop, frees it WHILE owed. -/
theorem Ledger.noPin_reincarnates :
    (Ledger.racer (Ledger.deferNoPin ⟨1, 0⟩)).freed
    ∧ 0 < (Ledger.deferNoPin (⟨1, 0⟩ : Ledger)).owing := by
  simp [Ledger.racer, Ledger.deferNoPin, Ledger.freed]

/-- The refcount FLOOR: a put of `k` refs on `old`, clamped at 0 (the `folios_put_refs` band-aid). -/
def floorPut (old k : Nat) : Nat := if k ≤ old then old - k else 0

/-- **THE FLOOR RE-FREES A STALE PUT.**  On an already-freed folio (`old = 0`) any deferred put `k > 0`
yields `floorPut 0 k = 0`, and the free path reads "refs reached 0" and frees it AGAIN — the double-free
(both freers `folios_put_refs`).  The floor converts the phantom's underflow into the double-free; the
PIN removes the precondition, since `owing_not_freed` keeps the folio non-zero while a discharge is
owed. -/
theorem floor_refrees_stale (k : Nat) (hk : 0 < k) : floorPut 0 k = 0 := by
  have h : ¬ (k ≤ 0) := by omega
  simp only [floorPut, if_neg h]

end GatherLedger
end Tessera


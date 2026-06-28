/-
  Tessera — COLLAPSE REF-PIN: wiring deferred-maintenance catalogue ROW #5 (deferred split / khugepaged
  collapse).

  Grounded in `mm/khugepaged.c` (`__collapse_huge_page_isolate`). To collapse 512 base pages into one
  2 MB huge page, khugepaged copies their contents into a fresh huge page, retracts the base PTEs under
  the pmd lock, and frees the base pages. Before isolating each base page it checks:

      if (folio_expected_ref_count(folio) != folio_ref_count(folio))
              result = SCAN_PAGE_COUNT;   // abort

  the EXACT-COUNT guard — identical in shape to migration's `folio_ref_freeze`: proceed only if the base
  page carries exactly the references khugepaged accounts for (no concurrent fault, GUP pin, or extra
  mapping), else abort. Freeing/repointing a base page another actor still holds would be a
  use-after-free / lost-write.

  What is distinctive: the collapse is driven by a LOCK-FREE SCANNER, so the guard splits into a
  speculative scan and a COMMIT-time re-check under the pmd lock that serialises the free. Safety rests
  on the commit check, not the scan — the formal point this file makes.
-/
import Tessera.Deferred
import Tessera.Incarnation

namespace Tessera
namespace Deferred

/-- A base page mid-collapse. `mapped` = the mappings the retract will clear (the owed maintenance);
`refsAtScan` = the refcount the lock-free scanner saw; `refsAtCommit` = the refcount re-read UNDER THE
PMD LOCK, at the irreversible retract+free. -/
structure Collapse where
  mapped       : Nat
  refsAtScan   : Int
  refsAtCommit : Int
deriving Repr

/-- `folio_expected_ref_count`: the references khugepaged accounts for — the mappings plus the
isolation/cache ref (`+1`). -/
def Collapse.expected (c : Collapse) : Int := (c.mapped : Int) + 1

/-- The collapse COMMITS (retract PTEs + free base page) only if the under-lock re-check finds the
refcount exactly `expected`. Otherwise `SCAN_PAGE_COUNT` — abort. -/
def Collapse.commits (c : Collapse) : Prop := c.refsAtCommit = c.expected

/-- The collapse as a `Deferred.Window`: the guard is the under-lock refcount, the owed maintenance is
the mappings the retract clears. -/
def Collapse.toWindow (c : Collapse) : Window := { refs := c.refsAtCommit, owed := c.mapped }

/-- **A committed collapse discharges `Pinned`** — exactly migration's freeze, but on the refcount read
UNDER THE PMD LOCK that serialises the free, with the cache ref as the surplus. -/
theorem collapse_committed_pinned (c : Collapse) (hc : c.commits) : c.toWindow.Pinned := by
  simp only [Collapse.commits, Collapse.expected] at hc
  simp only [Window.Pinned, Collapse.toWindow]; omega

/-- …so the base page is live across the copy+retract — it cannot be freed while mappings still owe
retraction (`pinned_live`). -/
theorem collapse_committed_live (c : Collapse) (hc : c.commits) (ho : 0 < c.mapped) :
    c.toWindow.live :=
  pinned_live c.toWindow (collapse_committed_pinned c hc) (by simp only [Collapse.toWindow]; omega)

/-- **A stray reference ABORTS the collapse** (`SCAN_PAGE_COUNT`): if a concurrent fault or GUP pin
raised the refcount above `expected`, the under-lock re-check fails and the collapse backs off rather
than freeing a base page another actor still holds. The migration-`-EAGAIN` analogue. -/
theorem collapse_aborts (c : Collapse) (hstray : c.expected < c.refsAtCommit) : ¬ c.commits := by
  simp only [Collapse.commits]; omega

/-- **Safety rests on the COMMIT check, not the scan.** Whether the collapse commits depends ONLY on the
under-lock `refsAtCommit`, never on the speculative `refsAtScan`: changing what the scan saw cannot
change the safety verdict. The scan is an optimisation; the commit-time guard is the proof. -/
theorem safety_independent_of_scan (c : Collapse) (s' : Int) :
    ({ c with refsAtScan := s' }).commits ↔ c.commits := by
  simp only [Collapse.commits, Collapse.expected]

/-- The lock-free scanner's verdict — it saw the base page at exactly `expected`. -/
def Collapse.commitsOnScan (c : Collapse) : Prop := c.refsAtScan = c.expected

/-- **THE BUG — trusting the speculative scan.** If a base page was clean at scan time
(`refsAtScan = expected`) but a fault/GUP raised its count by commit time (`expected < refsAtCommit`),
then the scan says "go" while the under-lock truth says "abort": committing on the scan frees/repoints a
page another actor now holds — use-after-free. The under-lock re-check is exactly what makes the
scan-trusting decision wrong. -/
theorem scan_trust_uaf (c : Collapse) (hscan : c.commitsOnScan) (hstray : c.expected < c.refsAtCommit) :
    c.commitsOnScan ∧ ¬ c.commits :=
  ⟨hscan, collapse_aborts c hstray⟩

/-- The commit-time re-check blocks reincarnation across the copy+retract: a base page held at exactly
`expected` cannot be freed+reused under another actor (`pinned_inc_correct`) — the same incarnation
guard as #143, migration, and writeback. -/
theorem collapse_inc_correct (c : Collapse) (p : Pfn) (e : Nat)
    (hc : c.commits) (ho : 0 < c.mapped) (hpr : p.refs = c.toWindow.refs) (he : p.inc = e) :
    IncCorrect p e ∧ ¬ CanReincarnate p :=
  pinned_inc_correct c.toWindow p e hpr he (collapse_committed_pinned c hc)
    (by simp only [Collapse.toWindow]; omega)

end Deferred
end Tessera

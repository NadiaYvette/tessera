/-
  Tessera — content COPY / MOVE: migration and the COW copy (pgcl #143 wrong-data).

  A third content-motion mechanism beside eviction/rematerialisation: **copying** a cluster's
  content from one physical frame range to another. Two real instances, ONE invariant:

    * **migration** (NUMA balance / compaction / hotplug) — move sub-page content old → new frame;
    * **the COW copy** (`do_wp_page`) — copy the shared page's content into a fresh private page.

  Both must be **sub-page-faithful**: destination sub-page `i` gets source sub-page `i`, never a
  cross. `Placement.lean` proved the *re-anchor* half (`cowRemap`: the PTE now points at the new
  base) — but a correct frame pointer to a frame holding the WRONG content (a folded copy) still
  feeds userspace wrong data. This file models the copy itself and proves both directions, then
  composes with placement into the same observable as `Eviction.lean`:

      observed(v) = intended(v)  ⟺  placement faithful  ∧  the content that reached the
                                     destination sub-frame is the right sub-page's

  so migration/COW join eviction under one rule: *content moves, but sub-page i stays sub-page i.*
-/
import Tessera.Eviction

namespace Tessera

/-- **Content copy / move** (migration, or the COW copy): move `n` sub-pages of content from
physical base `src` to physical base `dst`, sub-page `i` → sub-page `i`. Destination frame `dst+i`
receives source sub-page `src+i`; frames outside `[dst, dst+n)` are unchanged. -/
def copySub (mem : Mem) (src dst n : Nat) : Mem :=
  fun f => if dst ≤ f ∧ f < dst + n then mem (src + (f - dst)) else mem f

/-- **A correct content move is sub-page-faithful**: destination sub-page `i` holds exactly source
sub-page `i`'s content. -/
theorem copySub_faithful (mem : Mem) (src dst n i : Nat) (hi : i < n) :
    copySub mem src dst n (dst + i) = mem (src + i) := by
  simp only [copySub]
  rw [if_pos ⟨by omega, by omega⟩]
  congr 1
  omega

/-- **A correct migration / COW copy preserves the observable**: re-anchor placement to the new
base (`intendedFrame vb dst`, i.e. `Placement.cowRemap`) and faithfully copy the content
(`copySub`), and userspace observes exactly the intended content at the moved cluster. -/
theorem migrate_observed_intended {vb src dst n : Nat} {mem0 : Mem} (i : Nat) (hi : i < n) :
    observed (intendedFrame vb dst) (copySub mem0 src dst n) (vb + i)
      = intendedContent vb src mem0 (vb + i) := by
  simp only [observed, intendedContent, intendedFrame]
  have h : vb + i - vb = i := by omega
  rw [h]
  exact copySub_faithful mem0 src dst n i hi

/-- **The sub-page-CROSSING copy** (migration / COW copy bug): fill every destination sub-page from
source slot 0 (the sub-offset folded away), so destination sub-page `i` wrongly gets source
sub-page 0 — the content-copy twin of `Placement.cowFold` and `Eviction.remateFold`. -/
def copyFold (mem : Mem) (src dst n : Nat) : Mem :=
  fun f => if dst ≤ f ∧ f < dst + n then mem src else mem f

/-- **The crossing copy is a provable WRONG-DATA error**: when two source sub-pages differ, the
folded move puts the wrong content into a later destination sub-page — wrong data even though the
page "migrated" / was "copied". -/
theorem copyFold_wrong_data {mem0 : Mem} {src dst n : Nat}
    (hn : 1 < n) (hdiff : mem0 src ≠ mem0 (src + 1)) :
    copyFold mem0 src dst n (dst + 1) ≠ mem0 (src + 1) := by
  simp only [copyFold]
  rw [if_pos ⟨by omega, by omega⟩]
  exact hdiff

/-- **A crossing migration / COW copy breaks the observable** even with correctly re-anchored
placement: the content-move half is INDEPENDENTLY necessary, the same lesson as
`Eviction.content_fold_observed_wrong`, now for migration and COW. -/
theorem migrateFold_observed_wrong {vb src dst n : Nat} {mem0 : Mem}
    (hn : 1 < n) (hdiff : mem0 src ≠ mem0 (src + 1)) :
    observed (intendedFrame vb dst) (copyFold mem0 src dst n) (vb + 1)
      ≠ intendedContent vb src mem0 (vb + 1) := by
  simp only [observed, intendedContent, intendedFrame]
  have h : vb + 1 - vb = 1 := by omega
  rw [h]
  exact copyFold_wrong_data hn hdiff

end Tessera

/-
  Tessera — FILE-backed content: the vaddr ↔ file-offset mapping and catalog #15.

  The file content ROUND-TRIP (writeback out, fault-in back) is already `Eviction.lean`: a file is
  just another backing store, keyed by file offset instead of swap slot — `evict`/`rematerialise`
  and the observable carry over unchanged. What is FILE-specific, and not yet modeled, is the
  *address* mapping that picks which file sub-page a virtual address reads:

      a VMA based at `vm_start`, whose first granule is file granule `vm_pgoff`, maps virtual
      granule `v` to file granule  `vm_pgoff + (v − vm_start)`.

  Two sub-offsets meet here — the virtual one (`v − vm_start`) and the file one (`vm_pgoff`) — and
  conflating them is catalog **#15** ("vm_pgoff↔vm_start sub-page assumption → wrong-sub-page copy"):
  a fault that drops `vm_pgoff` (or crosses the two) reads the WRONG file sub-page, so two mappings
  of the same file disagree on its content. This file states the mapping, proves a faithful fault
  reads the intended file sub-page and that two VMAs over the same file granule agree, and shows the
  #15 drop is a provable wrong-data error — the file twin of `Placement.cowFold` / the swap folds.
-/
import Tessera.Eviction

namespace Tessera

/-- The INTENDED file granule for virtual granule `v` in a VMA based at `vm_start` whose first
granule is file granule `vm_pgoff`: `vm_pgoff + (v − vm_start)`. (Granule = sub-page unit.) -/
def fileGranule (vm_start vm_pgoff v : Nat) : Nat := vm_pgoff + (v - vm_start)

/-- What userspace observes at `v` for a file mapping: the page-cache content `fc` at the file
granule the fault mapped `v` to. -/
def fileObserved (fmap : Nat → Nat) (fc : Nat → Content) (v : Nat) : Content := fc (fmap v)

/-- **File mapping correctness**: a faithful fault maps each vaddr to its INTENDED file granule, so
userspace observes the intended file sub-page's content. -/
theorem file_observed_intended (vm_start vm_pgoff : Nat) (fc : Nat → Content) (v : Nat) :
    fileObserved (fileGranule vm_start vm_pgoff) fc v = fc (fileGranule vm_start vm_pgoff v) :=
  rfl

/-- **Shared-file consistency**: two VMAs that map the same file granule (`hsame`) read the same
content — the property #15 violates when one mapping crosses the sub-offset. -/
theorem file_shared_consistent (s1 pg1 s2 pg2 v1 v2 : Nat) (fc : Nat → Content)
    (hsame : fileGranule s1 pg1 v1 = fileGranule s2 pg2 v2) :
    fileObserved (fileGranule s1 pg1) fc v1 = fileObserved (fileGranule s2 pg2) fc v2 := by
  simp only [fileObserved]
  rw [hsame]

/-- **The catalog #15 bug**: a fault that computes the file granule as `v − vm_start`, DROPPING
`vm_pgoff` (assuming the VMA starts at file granule 0) — a sub-offset cross whenever `vm_pgoff ≠ 0`. -/
def fileGranuleFold (vm_start v : Nat) : Nat := v - vm_start

/-- **The #15 fold is a provable WRONG-DATA error**: at a VMA with a nonzero file offset, where the
file's granules differ there, the fault reads the WRONG file sub-page into userspace. -/
theorem fileFold_wrong_data {vm_start vm_pgoff : Nat} {fc : Nat → Content} {v : Nat}
    (hdiff : fc (v - vm_start) ≠ fc (vm_pgoff + (v - vm_start))) :
    fileObserved (fileGranuleFold vm_start) fc v ≠ fc (fileGranule vm_start vm_pgoff v) := by
  simp only [fileObserved, fileGranuleFold, fileGranule]
  exact hdiff

end Tessera

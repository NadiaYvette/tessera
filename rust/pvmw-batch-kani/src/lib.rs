//! Tessera ← pgcl #143: **Kani port of the PVMW batch-scan over-count model.**
//!
//! This is the tessera-side reciprocation of pgcl's `rmap-ab/formal/TESSERA-BRIDGE.md`
//! ask #2: "port the `nr_mmupages` batch scan to a Kani harness — it's pure index
//! arithmetic, ideal for Kani."  Faithful port of `surf-pfnalias/pvmw_batch_scan.c`.
//!
//! THE QUESTION (#143's refined obligation, inv2 / PTE-vector integrity): can
//! `nr_mmupages` — the count `page_vma_mapped_walk()` returns for one PVMW batch —
//! ever OVER-COUNT, i.e. exceed the present sub-PTEs of the *single* logical
//! cluster-mapping at the anchor?  An over-count makes the consumer
//! (`try_to_unmap_one` etc.) drop too many refs/rmaps on the anchor's `struct page`
//! → over-drop → freed-while-mapped → #143.
//!
//! Because `pte_pfn()` drops the sub-bits (F1), two PTEs of the *same folio* in a
//! *neighbouring VMA* can share `pte_pfn`; the `vma_address_end` clamp to `vm_end`
//! (F3) is what should stop the scan spilling into them.  Kani checks the faithful
//! (clamped) scan never over-counts — the same property pgcl's CBMC reports
//! `SUCCESSFUL` under `CLAMP=1` and `FAILED` under `CLAMP=0` (the clamp is
//! load-bearing).  Same bounded-model-checker (Kani == CBMC); Tessera's Lean is the
//! unbounded ∀N complement.
//!
//! Run: `cargo kani`.

pub const MMUSHIFT: u32 = 2;
pub const MMUCOUNT: u32 = 1 << MMUSHIFT; // PAGE_MMUCOUNT
pub const NSUB: usize = 3 * MMUCOUNT as usize; // anchor cluster + 2 clusters headroom

#[derive(Clone, Copy)]
pub struct Pte {
    pub cl_pfn: u32, // pte_pfn() result (sub bits dropped)
    pub present: bool,
    pub site: u8, // ground-truth logical mapping site (0 = hole)
}

/// The faithful kernel forward scan (mm/page_vma_mapped.c:294-368) returning
/// `nr_mmupages`, and the ground-truth count it must not exceed.  `clamp` honours the
/// `vma_address_end` → `vm_end` clamp (the faithful kernel = `true`).
#[cfg(kani)]
fn check(clamp: bool) {
    let fpfn_base: u32 = kani::any();
    let fnr: u32 = kani::any(); // folio_nr_pages
    kani::assume(fpfn_base >= 1 && fpfn_base < 8);
    kani::assume(fnr >= 1 && fnr <= 3);

    // anchor VMA window [0, vend_slot)
    let vend_slot: usize = kani::any();
    kani::assume(vend_slot >= 1 && vend_slot <= NSUB);

    // site 1: the anchor VMA's mapping of the folio (run [a1, a1+l1), pgoff skew k1)
    let a1: usize = kani::any();
    let k1: u32 = kani::any();
    let l1: usize = kani::any();
    kani::assume(k1 < MMUCOUNT);
    kani::assume(a1 < MMUCOUNT as usize); // anchor cluster in first window cluster
    kani::assume(l1 >= 1 && l1 <= (fnr * MMUCOUNT) as usize);
    kani::assume(a1 + l1 <= NSUB);
    kani::assume(a1 + l1 <= vend_slot); // site1 within the anchor VMA

    // site 2: OPTIONAL second mapping of the SAME folio, in a DIFFERENT VMA
    // (rmap_one is once-per-VMA), so it begins at/after the anchor VMA boundary.
    let have2: bool = kani::any();
    let a2: usize = kani::any();
    let k2: u32 = kani::any();
    let l2: usize = kani::any();
    kani::assume(k2 < MMUCOUNT);
    kani::assume(a2 <= NSUB && l2 >= 1 && l2 <= NSUB); // bound a2 BEFORE the arithmetic (no overflow)
    kani::assume(l2 <= (fnr * MMUCOUNT) as usize);
    kani::assume(a2 >= vend_slot && a2 + l2 <= NSUB); // a DIFFERENT VMA, at/after vm_end

    let mut t = [Pte { cl_pfn: 0xbad, present: false, site: 0 }; NSUB];

    // paint site 1
    let mut i = 0;
    while i < l1 {
        let s = a1 + i;
        let eff = s as u32 + k1;
        let cp = eff >> MMUSHIFT;
        if s < NSUB && cp < fnr {
            t[s] = Pte { cl_pfn: fpfn_base + cp, present: true, site: 1 };
        }
        i += 1;
    }
    // paint site 2 (same folio, only on holes)
    if have2 {
        let mut i = 0;
        while i < l2 {
            let s = a2 + i;
            let eff = s as u32 + k2;
            let cp = eff >> MMUSHIFT;
            if s < NSUB && cp < fnr && t[s].site == 0 {
                t[s] = Pte { cl_pfn: fpfn_base + cp, present: true, site: 2 };
            }
            i += 1;
        }
    }

    // anchor: a present site-1 slot in the first window cluster
    let anchor: usize = kani::any();
    kani::assume(anchor < MMUCOUNT as usize);
    kani::assume(anchor < vend_slot);
    kani::assume(t[anchor].present && t[anchor].site == 1);

    let match_pfn = t[anchor].cl_pfn; // pte_pfn(first)
    let anchor_cp = match_pfn; // the struct page the consumer charges

    // kernel `end` = folio projected end, clamped to vm_end (vma_address_end)
    let folio_end_slot = a1 + (fnr * MMUCOUNT) as usize;
    let mut end_slot = folio_end_slot;
    if clamp && end_slot > vend_slot {
        end_slot = vend_slot;
    }
    kani::assume(end_slot > anchor);

    // ===== faithful forward scan → nr_mmupages =====
    let sub_off = (anchor as u32) & (MMUCOUNT - 1);
    let mut n: usize = 1;
    let mut max = (MMUCOUNT - sub_off) as usize; // per-yield cap
    if anchor + max > end_slot {
        max = end_slot - anchor;
    }
    while n < max {
        let j = anchor + n;
        if !t[j].present {
            break;
        }
        if t[j].cl_pfn != match_pfn {
            break;
        }
        n += 1;
    }

    // ===== ground truth: sub-PTEs of the anchor's cluster page AND site, contiguous =====
    let mut truth: usize = 0;
    let mut i = anchor;
    while i < NSUB && i < end_slot {
        if !t[i].present || t[i].cl_pfn != anchor_cp || t[i].site != 1 {
            break;
        }
        truth += 1;
        i += 1;
    }

    // ===== INVARIANT: no over-count =====
    assert!(n <= truth);
}

/// **The faithful kernel scan never over-counts** — the `vm_end` clamp holds the batch
/// to the anchor mapping's own sub-PTEs (inv2).  Kani exhaustively explores every
/// page-table layout (folio size, two same-pfn sites, pgoff skews) up to the bound.
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(16)]
fn pvmw_batch_no_overcount_clamped() {
    check(true);
}

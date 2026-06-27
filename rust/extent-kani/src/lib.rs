//! Tessera — Layer I, literal-Rust validation via **Kani** (bounded model checking).
//!
//! telix's real `kernel/src/mm/extent.rs` is a raw-pointer B+-tree (17 `unsafe` blocks,
//! `*mut u8` nodes) — outside Aeneas's safe-Rust borrow model. The right tool for
//! *unsafe* kernel Rust is Kani, which model-checks the actual executable code.
//!
//! This crate carries a faithful, self-contained Rust implementation of the **ordered
//! extent-map insert** — the same algorithm proved in `proof/Tessera/ExtentMap.lean`
//! (`insert` / `insert_ordered`) — and a Kani harness proving that inserting a
//! *disjoint* extent **preserves the ordering invariant**, over all inputs (up to the
//! bound), with no integer overflow.  That is the literal-Rust counterpart of the Lean
//! theorem `ExtentMap.insert_ordered`: the algorithm holds not just on idealized Lean
//! data but on real executable Rust.
//!
//! To keep Kani's CBMC backend in budget, the verified path is **heap-free** (fixed
//! arrays, not `Vec`) and uses the consecutive-ordering form — which, for a base-sorted
//! map, is equivalent to the full `Pairwise (·.hi ≤ ·.lo)` of `ExtentMap.Ordered`
//! (each `eᵢ.hi ≤ eᵢ₊₁.lo` and `lo ≤ hi` chain to give every `eᵢ.hi ≤ eⱼ.lo`, i<j).
//!
//! Run: `cargo kani`.  Verifying telix's *deployed* `ExtentTree` in place additionally
//! needs its kernel deps (the node allocator, `PhysAddr`, `#![no_std]`) stubbed so the
//! module builds under a harness — the remaining step toward the literal module.
//!
//! `coalesce` carries telix's *actual* `can_coalesce`/`ExtentFlags` logic verbatim under
//! Kani — the first deployed-kernel functions verified directly.

pub mod coalesce;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Extent {
    pub base: u32,
    pub size: u32,
}

impl Extent {
    #[inline]
    pub fn lo(&self) -> u32 {
        self.base
    }
    #[inline]
    pub fn hi(&self) -> u32 {
        self.base + self.size
    }
}

/// Two extents are disjoint when their half-open intervals do not overlap
/// (mirrors `Tessera.Disjoint`).
pub fn disjoint(a: &Extent, b: &Extent) -> bool {
    a.hi() <= b.lo() || b.hi() <= a.lo()
}

/// Ordered insertion into a 3-element sorted map, keeping it sorted by base — the
/// heap-free, bounded instance of `Tessera.ExtentMap.insert`.  The result is always the
/// four extents in base order.
pub fn insert3(es: &[Extent; 3], e: Extent) -> [Extent; 4] {
    if e.base <= es[0].base {
        [e, es[0], es[1], es[2]]
    } else if e.base <= es[1].base {
        [es[0], e, es[1], es[2]]
    } else if e.base <= es[2].base {
        [es[0], es[1], e, es[2]]
    } else {
        [es[0], es[1], es[2], e]
    }
}

#[cfg(kani)]
mod verification {
    use super::*;

    /// A bounded, arbitrary extent with non-empty size and bounds chosen so `hi()`
    /// cannot overflow `u32` (Kani checks overflow; the real PFN space is far below).
    fn any_extent() -> Extent {
        let base: u32 = kani::any();
        let size: u32 = kani::any();
        kani::assume(size >= 1 && size <= (1u32 << 12));
        kani::assume(base <= (1u32 << 20));
        Extent { base, size }
    }

    /// **The literal-Rust counterpart of `ExtentMap.insert_ordered`** (bounded at three
    /// pre-existing extents): for every ordered map and every extent disjoint from all
    /// of it, the ordered insert yields an ordered map.  Kani proves this exhaustively
    /// over the bounded input space — and certifies no integer overflow on the way.
    #[kani::proof]
    fn insert_preserves_order() {
        let es = [any_extent(), any_extent(), any_extent()];
        // the input is ordered (consecutive non-overlapping ⇒ base-sorted)
        kani::assume(es[0].hi() <= es[1].lo());
        kani::assume(es[1].hi() <= es[2].lo());

        let e = any_extent();
        kani::assume(disjoint(&e, &es[0]));
        kani::assume(disjoint(&e, &es[1]));
        kani::assume(disjoint(&e, &es[2]));

        let out = insert3(&es, e);

        // the result is ordered (consecutive non-overlapping)
        assert!(out[0].hi() <= out[1].lo());
        assert!(out[1].hi() <= out[2].lo());
        assert!(out[2].hi() <= out[3].lo());
    }
}

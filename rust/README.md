# Tessera — Layer-I literal-Rust validation

The Lean development (`../proof/`) proves the VM **algorithm** and refines it down a
tower of models toward telix's implementation (`ExtentMap` → `BTree` → `Pte` →
`RadixPt`). This directory closes the last gap: validating **actual executable Rust**
against the same invariants.

## Why Kani, not Aeneas

The original plan named **Aeneas** (Rust → a pure functional model in Lean, via Charon).
Aeneas models *safe* Rust ownership/borrows. But telix's real
`kernel/src/mm/extent.rs` is a **raw-pointer B+-tree** — 17 `unsafe` blocks, 28
raw-pointer uses, `*mut u8` node allocation, transmute-style `as_interior`/`as_leaf`,
`unsafe impl Send/Sync`. That is exactly what Aeneas's borrow calculus excludes, so
Aeneas cannot produce a meaningful model of it.

The right tool for *unsafe* kernel Rust is **[Kani](https://model-checking.github.io/kani/)**
— a bounded model checker (CBMC backend) that verifies the actual executable code,
raw pointers and all, by exhaustively exploring inputs up to a bound.

## `extent-kani/`

A faithful, self-contained Rust implementation of the **ordered extent-map insert** —
the same algorithm as `proof/Tessera/ExtentMap.lean` (`insert` / `insert_ordered`) —
plus a Kani harness proving that inserting a *disjoint* extent **preserves the ordering
invariant** over all inputs up to a bounded size (and that no integer overflow occurs).

This is the **literal-Rust counterpart of the Lean theorem `insert_ordered`**: the
algorithm holds not only on idealized Lean data but on real executable Rust.

Run:
```
cd extent-kani && cargo kani
```

## Remaining

Verifying telix's *deployed* `ExtentTree` in place additionally needs its kernel
dependencies (the node allocator, `PhysAddr`, the `#![no_std]` environment) stubbed so
the module builds under Kani's harness. The harness here establishes the method and the
property; pointing it at the real module is the next step. (For a *full* — not bounded —
proof of the unsafe code, **Verus** is the alternative, at the cost of in-source
annotation.)

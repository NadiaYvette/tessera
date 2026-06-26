# Architecture coverage for Property-2 (herd7) and the cost of extending it

What `herd7` 7.58 (installed) models, by architecture and **level**, and what it would
take to cover telix's full set for TLB-shootdown work. The crucial distinction is
**user-level concurrency** (which `herd` has broadly) vs. the **system / virtual-memory
layer** (page-table descriptors, the translation walk, `TLBI`/`SFENCE.VMA`/`INVLPG`,
the relaxed-memory semantics of translation) — which is what Property 2 needs.

## What herd7 models

| Arch | Instruction semantics | User-level mem model | **VM / TLB model** |
|------|:--:|:--:|:--:|
| **AArch64** | yes | yes (Armv8-A) | ✅ **full VMSA** (`aarch64.cat`, `aarch64bbm.cat`, `…memattrs/hwreqs`) |
| AArch32 / ARM | yes | yes | partial (`aarch32.cat`) |
| **x86-64** | yes | yes (`x86tso.cat`) | ❌ none |
| **riscv64** | yes | yes (RVWMO `riscv.cat`, `riscv-tso`) | ❌ none |
| **mips64** | yes | yes (`mips.cat`, `mips-tso`) | ❌ none |
| PPC | yes | yes | ❌ none |
| **loongarch64** | ❌ **absent** | ❌ | ❌ |

So: **the system/VM layer is AArch64-only** (the relaxed-virtual-memory frontier was
done for Armv8-A — Simner/Armstrong/Sewell et al., ESOP 2022 — and nowhere else to that
maturity). For telix's set, the *user-level* models already exist for everything except
LoongArch; the *VM/TLB* layer exists only for AArch64.

## Cost of adding the VM/TLB layer, per architecture

The hard part is **not** the instruction parser (those exist for x86/riscv/mips) — it
is the **relaxed-memory semantics of translation**: how a translation walk reads PTEs,
how the TLB caches and is invalidated, and the ordering against barriers. That is a
multi-year research effort per architecture. Ranked by tractability:

1. **riscv64 — best non-Arm candidate (hard but tractable).** RVWMO base is present; the
   privileged spec (Sv39/48, `SFENCE.VMA`) is open and **actively being formalized** (the
   RISC-V memory-model TG; Sail models in `isla`). Building a herd RISC-V VM model means
   tracking that emerging work, not inventing from scratch.
2. **x86-64 — moderate first cut, hard to make faithful.** TSO base is simple and strong
   (less reordering than Arm), so a "good-enough for shootdown shapes" TSO+page-walk
   +`INVLPG` model is weeks of work. But x86's *architectural* TLB/page-walk guarantees
   are under-documented by Intel/AMD, so a *faithful* model is research.
3. **mips64 — interesting, because it's software-refill.** MIPS has **no hardware
   page-table walker**: the TLB is filled by a *software* refill handler using explicit
   `TLBWI`/`TLBWR`/`TLBINV` (COP0) instructions, over OS-chosen page tables. So the hard
   part of the Arm model — the *speculative hardware walk reading PTEs* — simply does not
   exist. The VM model reduces to the existing MIPS memory model **plus explicit
   TLB-management instruction events**, which is conceptually cleaner. herd lacks it, so
   it is real work (add the COP0 TLB semantics), but the *memory-model* burden is lighter.
   (The 1 KiB-PageGrain extension is orthogonal — a page-size feature, not a memory-model
   one; it does not change this analysis. It makes mips64 the most *compelling*
   demonstration target — see `../doc/mmu-variants.md` — but not harder to model.)
4. **loongarch64 — greenfield (very hard).** Not in herd at all: would need the
   instruction semantics, a base weak-memory model (LoongArch has a documented weak model,
   partially formalized), **and** a VM/TLB layer. LoongArch is *also* software-refill
   (same TLB-instruction structure as MIPS), so the VM layer shares the simpler character
   — but everything below it must be built first.

## Two things that make this far less daunting than "one research project per arch"

- **The protocol reasoning (Route B, Iris) is architecture-agnostic.** The shootdown's
  correctness depends on abstract ordering facts — *PT-write before local `TLBI` before
  completion-signal; a remote that observes the signal has observed the invalidation* —
  which can be proved over a **parameterised memory model**. Porting Route B to another
  architecture is then *instantiating the parameter*, not rebuilding the proof. So the
  general theorem is portable even where the litmus tooling is not.
- **Software-refill (mips64, loongarch64) is the cleaner regime — exactly the
  `mmu-variants.md` thesis.** With no hidden hardware walker, the relaxed-VM semantics
  collapse toward ordinary concurrency + explicit TLB-write/invalidate instructions. The
  "hardware walks page tables thus" assumption that the Arm model has to capture is
  *replaced by software we can model directly*. So the two arches with the least herd
  support are, paradoxically, the ones whose VM memory-model is most tractable to build —
  and where the user's standing latitude to build our own toolchain would pay off most.

## Recommendation

- **Now:** AArch64 for Route A (the only complete VM model); Route B (Iris) for the
  architecture-agnostic protocol theorem.
- **Best Route-A extension:** riscv64 (open, actively-formalised VM spec).
- **Highest-leverage build-our-own:** a software-refill VM model (mips64 — the
  PageGrain demonstration target, or loongarch64), where the memory-model is simplest and
  no mature alternative exists.

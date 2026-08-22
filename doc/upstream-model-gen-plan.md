# Upstream Model Generation Plan — `trust-line` G1 (pt_walk bridge)

**Status:** Plan / not started  
**Depends on:** `upstream_bridge.v`, `bitfield_bridge.v` (committed `491de50`, `53f96e3`)  
**Goal:** Mechanically prove that Tessera's `translate`/`walk_decision` agrees with
the **actual vendored `sail-riscv`** `pt_walk` (not just Tessera's own
transcription of the upstream predicates).

## 1. Why This Matters

The G1 trust line currently has two layers (decision bridge + bitfield bridge),
both **verbatim transcriptions** from `sail-riscv` into `machine.sail`.  The
transcription is a manual copy — *we* verified it's correct, but Rocq hasn't.
The upstream-bridge step closes this gap: **the vendored `sail-riscv` source is
generated to Rocq**, and a bridge lemma proves Tessera's translated walk
produces the same result as the real `vmem.sail` `pt_walk` on the same Sv39
inputs.

## 2. What We Have

| File | Role |
|---|---|
| `third_party/sail-riscv/model/sys/vmem.sail` | Upstream `pt_walk`, `PTW_Result`, `checkPTEPermission` |
| `third_party/sail-riscv/model/sys/vmem_pte.sail` | Upstream `PTE_Flags`, `PTE_Ext`, `pte_is_invalid`, `pte_is_non_leaf` |
| `upstream_bridge.v` | `walk_decision` ↔ `pte_is_invalid`/`pte_is_non_leaf` (transcribed, not generated) |
| `bitfield_bridge.v` | `bits(64) PTE word ↔ Pte` record (transcribed bitfields) |
| `machine.sail` | Our model: types + `translate`/`walk_decision` |

## 3. The Dependency Closure

`vmem.sail` imports (directly and transitively):

```
vmem.sail
├── prelude.sail (bitvector ops, option, list)
├── core.sail (mstatus, satp, menvcfg, hartSupports)
├── exceptions.sail (internal_error)
├── pmp.sail (pmp_check — pure but parameterised)
├── virtual_memory_types.sail (PTW_Result, PTW_Access)
├── vmem_pte.sail (PTE_Flags, PTE_Ext, pte check predicates)
└── sys/sys.sail (ties everything together)
```

**Total:** ~165 Sail files; `vmem.sail` + its transitive deps ~40 files.

### Externs / Callbacks

`vmem.sail` uses 18 externs (stubs that must be provided):

| Extern | Type | Difficulty |
|---|---|---|
| `menvcfg` | `() → menvcfg_bits` | Returns config; trivially stubable |
| `currentlyEnabled` | `() → bool` | `true` stub |
| `hartSupports` | `Ext_Zvpn → bool` | `true` for Sv39, `false` else |
| `mstatus` | `() → MStatus_bits` | Stub with TSR=TVM=0, MXR=SUM=1 |
| `internal_error` | `string → unit` | Pure no-op |
| `translate_callback` | `acc → paddr → PTW_Result` | **THE KEY EXTERN** — this is where we hook in |
| 12 more pmp/prelude externs | various | All trivially stubable |

The critical insight: **`translate_callback`** is the hook where the upstream
model delegates to the actual translation.  We can **replace it with our own
`walk_decision`**, making the upstream model call *our* logic — and then the
equivalence is trivial (identity).

## 4. Approach: Fragment Extraction (Option A)

Rather than generating the full 165-file model to Rocq (which would take forever
to compile and produce gigabytes of `.vo`), we extract just the **vmem fragment**:

1. **Copy the transitive dependency subgraph** (~40 files) into a new Sail file
   `hardware/src/upstream_vmem.sail`, inlining the externs as stubs.
2. **Replace `translate_callback`** with a call to `walk_decision` (from
   `machine.sail`).
3. **Generate to Rocq**: `sail upstream_vmem.sail --rocq -o upstream_vmem`
4. **Prove the bridge lemma**: the generated `pt_walk` calls our
   `walk_decision` → the result tuple equals Tessera's `translate` output.

### Sub-option A.1: Verbatim Sail → Rocq (recommended)

- Copy the Sail sources, stub the externs, generate the whole closure.
- Prove `upstream_pt_walk_agrees_with_translate` in Rocq.
- **Pro:** fully mechanical, no hand-transcription.
- **Con:** large generated file (~5000 lines), compilation time (~60s).

### Sub-option A.2: Sail → OCaml test oracle

- Generate `upstream_vmem` to OCaml (not Rocq).
- Write a QEMU-style diff-test: feed random PTEs to both OCaml oracle and
  Rocq `translate`, assert agreement on 100k vectors.
- **Pro:** fast, simple, covers the ground truth.
- **Con:** not a Rocq proof; weaker than the G1 ideal.

## 5. Approach: The `translate_callback` Trick (Option B, simpler)

Even simpler: instead of extracting the fragment, **instrument `machine.sail`**
to also generate the upstream `pt_walk` by adding it directly alongside
`translate`, with stubbed externs, and call `walk_decision` as the callback.

1. Add `pt_walk`, `PTW_Result`, `checkPTEPermission` verbatim from `vmem.sail`
   into `machine.sail` (or a companion `upstream_ptw.sail`).
2. Stub all externs.
3. Set `translate_callback` to call `walk_decision`.
4. Generate to Rocq.
5. Prove the bridge lemma.

This is **Option B** from `rigor-trust-line.md`.

## 6. Decision

**Recommendation:** Start with **Option B** (inline into the Tessera Sail model).
It's the smallest delta, reuses the existing build infrastructure, and directly
proves the bridge lemma in Rocq.

If the extern stubbing proves too complex (the full `vmem.sail` has subtle
dependencies we can't easily stub), fall back to Option A.2 (OCaml oracle
diff-test).

## 7. Step-by-Step Plan (Option B)

### Step B.1: Scout the Upstream `pt_walk`

- Copy `PTW_Access`, `PTW_Result`, `pt_walk` from `vmem.sail` into a temporary
  Sail file.
- Identify every extern call and add a stub.
- Get it to typecheck in isolation.

### Step B.2: Integrate into Machine Model

- Add the stubbed `pt_walk` to `machine.sail` (or `upstream_ptw.sail`).
- Wire `translate_callback` to call `walk_decision`.
- Regenerate machine.v.

### Step B.3: Prove the Bridge Lemma

- `upstream_ptw_bridge.v`: for all `satp_ppn`, `va`, `mem`, the upstream
  `pt_walk` returns the same result as Tessera's `translate`.
- This is essentially a **reflexivity** proof when `translate_callback` is
  wired — but Rocq will need to see through the generated code.

### Step B.4: Wire into build.sh

- Add the Sail file to the build.
- Add axiom hygiene checks.
- Full build passes.

## 8. Risk / Open Questions

- **`read_pte` extern**: upstream `pt_walk` uses `read_pte` which takes a
  `paddr` and returns `option PTE_Bits`. Tessera's `read_pte` has the same
  signature.  Can we share the function?
- **`checkPTEPermission`**: upstream checks R/W/X permissions against the
  access type. Tessera's `walk_decision` doesn't do permission checks yet.
  For the bridge we may need to restrict to `Execute` access or stub the
  permission check.
- **Virtual memory enable/disable**: upstream checks `mstatus.TVM` and `satp.MODE`
  before walking. Tessera assumes Sv39 always enabled.  We may need to
  restrict to Sv39 mode for the bridge lemma.

## 9. Estimated Effort

| Step | Estimated Time |
|---|---|
| B.1 Scout | 1 session (30 min) |
| B.2 Integrate | 1 session |
| B.3 Bridge lemma | 2 sessions |
| B.4 Build wiring | 0.5 session |
| **Total** | **~4 sessions** |
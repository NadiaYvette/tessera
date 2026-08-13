# third_party/ — pinned upstreams

Vendored as git submodules so the verification is reproducible against exact
upstream commits. Clone with:

    git submodule update --init --recursive

| Path | Upstream | Pin | Role in Tessera |
|------|----------|-----|-----------------|
| `sail` | https://github.com/rems-project/sail | `0.20.2` | The Sail toolchain (Rocq backend) used by `hardware/` |
| `sail-riscv` | https://github.com/riscv/sail-riscv | `0.13` | Open RISC-V ISA model — first MMU variant (Sv39/Sv48) |
| `sail-arm` | https://github.com/rems-project/sail-arm | `1bf2e55` | AArch64 ISA model (hardware-walker variant) |
| `sail-cheri-mips` | https://github.com/CTSRD-CHERI/sail-cheri-mips | `13a9c3fb` | MIPS/CHERI model (software-refill TLB variant) |
| `sail-x86-from-acl2` | https://github.com/rems-project/sail-x86-from-acl2 | `0c6c023` | x86 model (the author's home arch) |
| `coq-sail` | https://github.com/rems-project/coq-sail | `0.20.2-rocq` | `SailStdpp` Rocq support library (opam `rocq-sail-stdpp`) |
| `rmem` | https://github.com/rems-project/rmem | `b2d3463` | Relaxed-memory / concurrency exploration |
| `isla` | https://github.com/rems-project/isla | `f189d5c` | Symbolic execution over Sail models |
| `islaris` | https://github.com/rems-project/islaris | `c978e10` | Sail→Iris bridge (verified assembly) |
| `iris` | https://gitlab.mpi-sws.org/iris/iris | `fdc7d5868` | Higher-order concurrent separation logic |

Notes:
- `sail`, `sail-riscv`, and `coq-sail` are pinned at release tags; the rest at the
  upstream HEAD captured at the time of vendoring (2026-08-13).
- The `SailStdpp` library actually consumed by `hardware/rocq/build.sh` is the opam
  `rocq-sail-stdpp` package; `coq-sail` is vendored here as its source of truth.

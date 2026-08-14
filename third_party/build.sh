#!/usr/bin/env bash
# Build the vendored Rocq stack from third_party/ submodules, in dependency order:
#
#     stdpp (9c7afbb6)  ->  iris (fdc7d5868)  ->  SailStdpp (coq-sail 0.20.2)
#                                                   ->  gpfsl (907eac66)
#
# stdpp, iris and SailStdpp are *installed* into the rocq-9.2 switch's
# user-contrib (backing up whatever was there first) so that (a) hardware/rocq/
# build.sh's explicit `-Q $UC/...` flags resolve, and (b) the dune-built SailStdpp
# and the coq_makefile-built gpfsl find stdpp/iris through the default Coq library
# path.  gpfsl itself is *not* installed: the S2.2 proofs reference it in-tree via
# `-Q third_party/gpfsl/gpfsl gpfsl`.
#
# Preconditions:
#   - submodules checked out: third_party/{stdpp,iris,coq-sail,gpfsl} (+ the sail
#     models used by hardware/src/machine.sail).
#   - the rocq-9.2 switch active: `eval "$(opam env --switch=rocq-9.2)"`.
set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"   # third_party/
UC="${ROCQ_UC:-$HOME/.opam/rocq-9.2/lib/coq/user-contrib}"
JOBS="-j$(nproc)"

command -v rocq >/dev/null || { echo "rocq not on PATH (eval \$(opam env --switch=rocq-9.2))" >&2; exit 1; }
command -v dune >/dev/null || { echo "dune not on PATH" >&2; exit 1; }

# install_theory SRC DEST  — copy the Coq artifacts (.v/.vo/.vos/.vok/.glob) of one
# theory directory into user-contrib, backing up an existing install the first time.
install_theory() {
  local src="$1" dest="$2"
  if [ -e "$dest" ] && ! compgen -G "$dest.bak.*" >/dev/null; then
    mv "$dest" "$dest.bak.$(date +%s)"
    echo "  backed up $dest -> $dest.bak.*"
  fi
  mkdir -p "$dest"
  find "$src" -maxdepth 1 -type f \
    \( -name '*.v' -o -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' \) \
    -exec cp -a {} "$dest"/ \;
  echo "  installed $(find "$dest" -maxdepth 1 -name '*.vo' | wc -l) .vo -> $dest"
}

echo "==> [1/4] stdpp @ $(git -C "$REPO/stdpp" rev-parse --short HEAD)"
make -C "$REPO/stdpp" $JOBS
install_theory "$REPO/stdpp/stdpp"           "$UC/stdpp"
install_theory "$REPO/stdpp/stdpp_bitvector" "$UC/stdpp/bitvector"
install_theory "$REPO/stdpp/stdpp_unstable"  "$UC/stdpp/unstable"

echo "==> [2/4] iris @ $(git -C "$REPO/iris" rev-parse --short HEAD)"
make -C "$REPO/iris" $JOBS
install_theory "$REPO/iris/iris"            "$UC/iris"
install_theory "$REPO/iris/iris_heap_lang"  "$UC/iris/heap_lang"
install_theory "$REPO/iris/iris_unstable"   "$UC/iris/unstable"
install_theory "$REPO/iris/iris_deprecated" "$UC/iris/deprecated"

echo "==> [3/4] SailStdpp (coq-sail @ $(git -C "$REPO/coq-sail" rev-parse --short HEAD))"
( cd "$REPO/coq-sail" && dune build )
install_theory "$REPO/coq-sail/_build/default/src-stdpp" "$UC/SailStdpp"

echo "==> [4/4] gpfsl @ $(git -C "$REPO/gpfsl" rev-parse --short HEAD)"
make -C "$REPO/gpfsl" $JOBS

echo
echo "OK: vendored stack built. stdpp/iris/SailStdpp installed under $UC;"
echo "    gpfsl built in-tree.  Now run hardware/rocq/build.sh (machine model)."

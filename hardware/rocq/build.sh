#!/usr/bin/env bash
# Build the Tessera hardware-state model: Sail -> Rocq -> checked .vo
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"   # hardware/rocq
HW="$(dirname "$HERE")"                                 # hardware
SRC="$HW/src/machine.sail"

# --- 1. locate the Rocq user-contrib libraries (SailStdpp, stdpp, iris) ---
UC="${ROCQ_UC:-$HOME/.opam/rocq-9.2/lib/coq/user-contrib}"
if [ ! -d "$UC/SailStdpp" ]; then
  echo "SailStdpp support library not found at $UC/SailStdpp" >&2
  echo "Install it with:  opam install rocq-sail-stdpp" >&2
  exit 1
fi

# --- 2. typecheck the Sail source ---
sail --just-check "$SRC"

# --- 3. generate Rocq (SailStdpp style) ---
sail "$SRC" --rocq --rocq-output-dir "$HERE" -o machine

# --- 4. compile the generated Rocq against SailStdpp + stdpp + iris ---
# (run from $HERE so machine.v can resolve `Require Import machine_types`)
cd "$HERE"
FLAGS="-Q $UC/stdpp stdpp -Q $UC/SailStdpp SailStdpp -Q $UC/iris iris"
rocq compile $FLAGS machine_types.v
rocq compile $FLAGS machine.v
rocq compile $FLAGS coherence.v
rocq compile $FLAGS coherence_leaf.v
rocq compile $FLAGS shootdown.v

echo "OK: hardware model generated and checked."

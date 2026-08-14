#!/usr/bin/env bash
# Build the Tessera hardware-state model: Sail -> Rocq -> checked .vo,
# then enforce axiom hygiene on every headline theorem.
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

# Dev stdpp (9c7afbb6) lowered its singleton notations {[ x ]} / {[ k := a ]}
# to level 0, while Sail emits record-update notations
# {[ r 'with' field := e ]} at level 1; the two then have an incompatible
# prefix and {[ k := a ]} stops parsing.  Move the (unused) record-update
# notations to level 0 to restore coexistence with stdpp's singletons.
sed -i 's/\(Build_.*\)(at level 1)\./\1(at level 0)./' "$HERE/machine_types.v"

# --- 4. compile the generated Rocq against SailStdpp + stdpp + iris ---
# (run from $HERE so machine.v can resolve `Require Import machine_types`)
cd "$HERE"
FLAGS="-Q $UC/stdpp stdpp -Q $UC/SailStdpp SailStdpp -Q $UC/iris iris"
rocq compile $FLAGS machine_types.v
rocq compile $FLAGS machine.v
rocq compile $FLAGS coherence.v
rocq compile $FLAGS coherence_leaf.v
rocq compile $FLAGS shootdown.v
rocq compile $FLAGS shootdown_iris.v

# --- 5. axiom hygiene: every headline theorem must be closed under the global
# context (no Axiom / Parameter / Admitted / admit). This is the machine-checked
# "axiom-free" claim, enforced on every build rather than by hand. ---
axiom_free() { # $1 = module (no .v), $2 = theorem, $3 = optional flags
  local mod="$1" thm="$2" flags="${3:-$FLAGS}" out
  cat > _axioms.v <<EOF
Require Import $mod.
Print Assumptions $thm.
EOF
  if ! out="$(rocq compile $flags _axioms.v 2>&1)"; then
    echo "CHECK FAILED: $mod.$thm did not compile:" >&2
    printf '%s\n' "$out" >&2
    rm -f _axioms.v _axioms.vo _axioms.vos _axioms.vok _axioms.glob ._axioms.aux
    return 1
  fi
  rm -f _axioms.v _axioms.vo _axioms.vos _axioms.vok _axioms.glob ._axioms.aux
  if printf '%s' "$out" | grep -q "Axioms:"; then
    echo "AXIOM LEAK: $mod.$thm is not axiom-free:" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
  if ! printf '%s' "$out" | grep -q "Closed under the global context"; then
    echo "CHECK FAILED: could not confirm $mod.$thm is closed under the global context" >&2
    printf '%s\n' "$out" >&2
    return 1
  fi
  echo "  axiom-free: $mod.$thm"
}

echo "--- axiom hygiene ---"
axiom_free coherence       unmap_correct
axiom_free coherence       unmap_without_flush_breaks_coherence
axiom_free coherence_leaf  unmap_leaf_correct
axiom_free coherence_leaf  unmap_leaf_without_flush_breaks_coherence
axiom_free coherence_leaf  invalidate_leaf_faults
axiom_free coherence_leaf  invalidate_leaf_correct
axiom_free shootdown       shootdown_correct
axiom_free shootdown       sfence_vma_va_empty
axiom_free shootdown       map_sfence_empty
axiom_free shootdown       shootdown_empty_cores
axiom_free shootdown       invalidate_shootdown_correct
axiom_free shootdown       invalidate_shootdown_empty_cores
axiom_free shootdown_iris  wait_spec
axiom_free shootdown_iris  pending_token_delete
axiom_free shootdown_iris  auth_frag_gset_to_gmap
axiom_free shootdown_iris  pending_tokens_split
axiom_free shootdown_iris  remote_spec
axiom_free shootdown_iris  wait_cnt_spec
axiom_free shootdown_iris  fork_remotes_spec
axiom_free shootdown_iris  broadcast_spec
axiom_free shootdown_iris  broadcast_reifies_machine

# --- 6. S2.2: the weak-memory (gpfsl/ORC11) shootdown, over the generated machine ---
# Requires the vendored gpfsl to be built first: third_party/build.sh.
REPO="$(dirname "$HW")"
GP="${GPFSL:-$REPO/third_party/gpfsl/gpfsl}"
if [ -d "$GP" ]; then
  WFLAGS="-Q $GP gpfsl $FLAGS"
  rocq compile $WFLAGS shootdown_weak.v
  axiom_free shootdown_weak shootdown_weak_gen_inv "$WFLAGS"
  axiom_free shootdown_weak invalid_pte_not_valid "$WFLAGS"
else
  echo "(skip S2.2: gpfsl not found at $GP — run third_party/build.sh first)" >&2
fi

echo "OK: hardware model generated and checked (axiom-free)."

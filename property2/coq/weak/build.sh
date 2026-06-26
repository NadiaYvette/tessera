#!/usr/bin/env bash
# Build the P2.4 weak-memory (iRC11/gpfsl) proofs in the dedicated `wm` switch.
# Keeps the stable `surd` switch (the SC proofs) untouched.
set -e
eval "$(opam env --switch=wm)"
echo "coq: $(coqc --version | head -1)"
for f in mp_weak.v tlb_shootdown_weak.v; do
  [ -f "$f" ] || { echo "(skip $f — not present yet)"; continue; }
  echo "=== coqc $f ==="
  coqc -Q . "" "$f"
  echo "    OK"
done
echo "weak-memory proofs: done."

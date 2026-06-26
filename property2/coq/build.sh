#!/bin/sh
# Build the Property-2 Iris proofs (Coq 8.20 + coq-iris 4.4 + coq-iris-heap-lang, opam switch surd).
eval $(opam env --switch=surd)
for f in HelloIris.v mp.v tlb_shootdown.v; do
  printf '%-20s ' "$f"
  coqc "$f" >/dev/null 2>&1 && echo "OK" || { echo "FAIL"; coqc "$f"; }
done

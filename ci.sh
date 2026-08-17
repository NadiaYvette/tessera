#!/usr/bin/env bash
# Tessera CI / regression runner.
#
# Runs every proof track and fails if any fails. Wirable into GitHub Actions,
# SourceHut builds, etc. — it is intentionally a plain script with no host
# assumptions beyond the opam switches already used by each track.
#
# Tracks:
#   1. hardware/rocq   — Sail -> Rocq -> .vo, plus axiom hygiene (build.sh)
#   2. property2/coq   — Iris proofs, Coq 8.20 ('surd' switch)
#   3. property2/cbmc  — CBMC regression harnesses (skipped if cbmc absent)
#   4. proof/          — Lean 4 (lake build) + #print axioms (no sorryAx)
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$HERE"

overall=0
step() { printf '\n===== %s =====\n' "$*"; }

# 1. Hardware model + Rocq proofs
step "hardware/rocq (Sail -> Rocq, coherence + shootdown + iris, axiom hygiene)"
if bash hardware/rocq/build.sh; then
  echo "PASS: hardware/rocq"
else
  echo "FAIL: hardware/rocq"
  overall=1
fi

# 1b. Live QEMU differential test for the MIPS decode (skips if ~/src/QEMU absent).
step "hardware/qemu-diff (live MIPS compute_pagemask differential test)"
if bash hardware/qemu-diff/run_mips_decode_diff.sh; then
  echo "PASS: hardware/qemu-diff"
else
  echo "FAIL: hardware/qemu-diff"
  overall=1
fi

# 2. Property-2 Iris proofs (Coq 8.20, 'surd' switch)
step "property2/coq (Iris)"
if (cd property2/coq && bash build.sh); then
  echo "PASS: property2/coq"
else
  echo "FAIL: property2/coq"
  overall=1
fi

# 3. Property-2 CBMC harnesses (regression; needs cbmc)
step "property2/cbmc (CBMC regression)"
if command -v cbmc >/dev/null 2>&1; then
  if (cd property2/cbmc && bash run.sh); then
    echo "PASS: property2/cbmc"
  else
    echo "FAIL: property2/cbmc"
    overall=1
  fi
else
  echo "SKIP: cbmc not installed (dnf install cbmc)"
fi

# 4. Lean proofs
step "proof/ (Lean 4)"
if (cd proof && lake build); then
  echo "PASS: proof (lake build)"
else
  echo "FAIL: proof (lake build)"
  overall=1
fi

# 5. Lean axiom hygiene: no sorryAx anywhere in the root import
step "proof/ axiom hygiene (no sorryAx)"
AX="$(mktemp /tmp/tessera_axiom_check.XXXXXX.lean)"
AXOUT="$(mktemp /tmp/tessera_axiom_check.XXXXXX.out)"
cat > "$AX" <<'EOF'
import Tessera
#print axioms Tessera.WF_split_at
EOF
if ! (cd proof && lake env lean "$AX" >"$AXOUT" 2>&1); then
  echo "FAIL: proof/ axiom check did not run:"
  cat "$AXOUT"
  overall=1
elif grep -q sorryAx "$AXOUT"; then
  echo "FAIL: proof/ contains sorryAx"
  overall=1
else
  echo "PASS: proof/ axiom hygiene"
fi
rm -f "$AX" "$AXOUT"

echo
if [ "$overall" -eq 0 ]; then
  echo "CI OK"
else
  echo "CI FAIL"
fi
exit "$overall"

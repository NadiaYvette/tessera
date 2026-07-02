#!/bin/sh
# Tessera Property 2 — CBMC harnesses for the count-correct per-gather PIN (r3pin, pgcl #143).
#
# Each harness mirrors Tessera/GatherLedger.lean (the `Ledger` section) and
# property2/coq/pin_ledger.v on the REAL folios_put_refs FLOOR arithmetic, letting CBMC
# enumerate every nondeterministic racer interleaving.  Install cbmc with `dnf install cbmc`.
#
# Expected outcomes (this is a regression test — it PASSES when they all match):
#   pin_reincarnation PIN=0  -> FAILED      (the current kernel: an over-drop frees the
#                                            cluster while a gather still owes it => the
#                                            r2diag2 reincarnation double-free; proves the
#                                            harness actually bites)
#   pin_reincarnation PIN=1  -> SUCCESSFUL  (r3pin: the dedicated pin ref absorbs the
#                                            over-drop => owing_not_freed, no double-free)
#   pin_crossgather   PIN=1  -> SUCCESSFUL  (r3pin does not break the balanced cross-gather
#                                            case: two mms, freed exactly once)
set -u
echo "## cbmc: $(cbmc --version 2>/dev/null || echo 'NOT INSTALLED — dnf install cbmc')"
fail=0
check() { # label expected args...
  label=$1; expect=$2; shift 2
  got=$(cbmc "$@" 2>/dev/null | grep -oE 'VERIFICATION (SUCCESSFUL|FAILED)' | awk '{print $2}')
  if [ "$got" = "$expect" ]; then printf 'PASS  %-40s (%s)\n' "$label" "$got"
  else printf 'FAIL  %-40s (got %s, want %s)\n' "$label" "${got:-none}" "$expect"; fail=1; fi
}
check "pin_reincarnation PIN=0 (bug present)"  FAILED     pin_reincarnation.c -DPIN=0 --unwind 3
check "pin_reincarnation PIN=1 (pin fixes it)" SUCCESSFUL pin_reincarnation.c -DPIN=1 --unwind 3
check "pin_crossgather   PIN=1 (clean case)"   SUCCESSFUL pin_crossgather.c   -DPIN=1
[ "$fail" -eq 0 ] && echo "SUITE OK" || echo "SUITE FAIL"
exit "$fail"

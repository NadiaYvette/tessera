#!/bin/sh
# Run the Property-2 TLB-shootdown litmus tests against the Armv8-A VMSA model.
export PATH="$HOME/.local/bin:$PATH"
for f in *.litmus; do
  printf '%-26s ' "$f"
  herd7 -variant vmsa "$f" 2>&1 | grep -E '^Observation' || echo '(error)'
done

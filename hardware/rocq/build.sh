#!/usr/bin/env bash
# Build the Tessera hardware-state model: Sail -> Rocq -> checked .vo,
# then enforce axiom hygiene on every headline theorem.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"   # hardware/rocq
HW="$(dirname "$HERE")"                                 # hardware
REPO="$(dirname "$HW")"                                 # repo root
SRC="$HW/src/machine.sail"

# --- 1. build/install the vendored Rocq stack (stdpp -> iris -> SailStdpp -> gpfsl).
# When the third_party submodules are checked out, delegate the whole stack to
# third_party/build.sh, which is the single source of truth for the dev stdpp/iris
# the S2.2 proofs need and installs them into user-contrib.  It is idempotent
# (make/dune are incremental), so on a warmed tree this is a fast no-op; on a clean
# checkout it does the one full build.  If the submodules are absent, fall back to
# whatever opam has installed.
UC="${ROCQ_UC:-$HOME/.opam/rocq-9.2/lib/coq/user-contrib}"
export ROCQ_UC="$UC"
if [ -d "$REPO/third_party/stdpp" ] && [ -d "$REPO/third_party/iris" ]; then
  bash "$REPO/third_party/build.sh"
fi
if [ ! -d "$UC/SailStdpp" ]; then
  echo "SailStdpp support library not found at $UC/SailStdpp" >&2
  echo "Install it with:  opam install rocq-sail-stdpp" >&2
  echo "(or check out the third_party submodules so third_party/build.sh provides it)" >&2
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
rocq compile $FLAGS machine_encoding.v
rocq compile $FLAGS coherence.v
rocq compile $FLAGS coherence_leaf.v
rocq compile $FLAGS tlb_tags.v
rocq compile $FLAGS shootdown.v
rocq compile $FLAGS machine_reify.v
rocq compile $FLAGS data_ram.v
rocq compile $FLAGS ipi.v
rocq compile $FLAGS conformance.v
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
axiom_free machine_reify    broadcast_reifies_machine
axiom_free machine_encoding invalid_pte_not_valid
axiom_free data_ram         read_byte_after_write
axiom_free data_ram         read_byte_after_write_other
axiom_free data_ram         invalidate_shootdown_load_faults
axiom_free data_ram         load_byte_mmio_faults
axiom_free data_ram         store_byte_mmio_noop
axiom_free data_ram         load_byte_after_store_byte
axiom_free ipi              receive_ipi_before_delivery_noop
axiom_free ipi              receive_ipi_after_delivery_sfences
axiom_free ipi              list_nth_bool_update_self
axiom_free ipi              receive_ipi_cores_true_eq_sfence_at
axiom_free ipi              ipi_broadcast_refines_invalidate_shootdown
axiom_free ipi              ipi_broadcast_correct
axiom_free ipi              test_vector_deliver_ipi
axiom_free ipi              test_vector_receive_before_delivery
axiom_free ipi              test_vector_receive_after_delivery
axiom_free ipi              test_vector_ipi_broadcast
axiom_free conformance      translate_conforms
axiom_free conformance      oracle_non_leaf_is_negb_is_leaf
axiom_free conformance      test_vector_mapping_ok
axiom_free conformance      test_vector_writeonly_faults
axiom_free conformance      test_vector_writeonly_exec_faults
axiom_free conformance      test_vector_missing_pte_faults
axiom_free conformance      test_vector_superpage_faults
axiom_free conformance      test_vector_execonly
axiom_free conformance      test_vector_writeonly_conforms
axiom_free tlb_tags         flush_tlb_entry_leaf
axiom_free tlb_tags         flush_tlb_entry_vivt_leaf
axiom_free tlb_tags         filter_tlb_leaf
axiom_free tlb_tags         test_vector_pipt_vivt_agree
axiom_free tlb_tags         test_vector_pipt_vivt_differ

# --- 6. S2.2: the weak-memory (gpfsl/ORC11) shootdown, over the generated machine ---
# gpfsl is built in-tree by third_party/build.sh (step 1 above); reference it via -Q.
GP="${GPFSL:-$REPO/third_party/gpfsl/gpfsl}"
if [ -d "$GP" ]; then
  WFLAGS="-Q $GP gpfsl $FLAGS"
  rocq compile $WFLAGS shootdown_weak.v
  axiom_free shootdown_weak shootdown_weak_gen_inv "$WFLAGS"
  axiom_free shootdown_weak shootdown_weak_ack_gen_inv "$WFLAGS"
  # per-cell coupling: the full TLB encoding carries the virtual address.
  axiom_free shootdown_weak encode_tlb_None_ne_Some "$WFLAGS"
  axiom_free shootdown_weak encode_tlb_None_eq "$WFLAGS"
  axiom_free shootdown_weak encode_tlb_test_vector_zero "$WFLAGS"
  axiom_free shootdown_weak encode_tlb_test_vector_carries_va "$WFLAGS"
  # S2.2c: the N-core weak-memory broadcast shootdown over the concrete machine.
  rocq compile $WFLAGS shootdown_weak_broadcast.v
  axiom_free shootdown_weak_broadcast bc_remote_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast bc_wait_all_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast bc_init_acks_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast bc_fork_remotes_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast bc_broadcast_spec "$WFLAGS"
  # S2.4: the weak-memory broadcast's ghost step is the IPI deliver+receive,
  # and the final machine is the pure IPI broadcast that reifies the conclusion.
  axiom_free shootdown_weak_broadcast bc_machine_ipi_step "$WFLAGS"
  axiom_free shootdown_weak_broadcast bc_machine_ipi_broadcast "$WFLAGS"
  axiom_free shootdown_weak_broadcast bc_post_reifies "$WFLAGS"
  # S2.4 -> S2.3b: the post-machine is exactly ipi_broadcast of the pre-machine,
  # so the coherence conclusion follows from ipi_broadcast_correct (S2.3b).
  axiom_free shootdown_weak_broadcast bc_post_machine_is_ipi_broadcast "$WFLAGS"
  axiom_free shootdown_weak_broadcast bc_post_reifies_via_ipi_broadcast "$WFLAGS"
  # per-cell coupling: the ack cell's released branch carries the va-flushed TLB
  # entry (flush_tlb_entry (Some (leaf_entry va)) va), bridged to encode_tlb None
  # via tlb_tags.flush_tlb_entry_leaf (checked in the pure section above).
else
  echo "(skip S2.2: gpfsl not found at $GP — check out the third_party/gpfsl submodule)" >&2
fi

echo "OK: hardware model generated and checked (axiom-free)."

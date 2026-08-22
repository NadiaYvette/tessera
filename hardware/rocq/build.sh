#!/usr/bin/env bash
# Build the Tessera hardware-state model: Sail -> Rocq -> checked .vo,
# then enforce axiom hygiene on every headline theorem.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"   # hardware/rocq
HW="$(dirname "$HERE")"                                 # hardware
REPO="$(dirname "$HW")"                                 # repo root
SRC="$HW/src/machine.sail"
MIPS_SRC="$HW/src/mips_tlb.sail"
LA_SRC="$HW/src/loongarch_tlb.sail"
AA_SRC="$HW/src/aarch64_tlb.sail"
SA_SRC="$HW/src/sail_arm_tlb.sail"
INTC_SRC="$HW/src/intc.sail"
TIMER_SRC="$HW/src/timer.sail"

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

# --- 2. typecheck the Sail sources ---
sail --just-check "$SRC"
sail --just-check "$MIPS_SRC"
sail --just-check "$LA_SRC"
sail --just-check "$AA_SRC"
sail --just-check "$SA_SRC"
sail --just-check "$INTC_SRC"
sail --just-check "$TIMER_SRC"

# --- 3. generate Rocq (SailStdpp style) ---
sail "$SRC" --rocq --rocq-output-dir "$HERE" -o machine
sail "$MIPS_SRC" --rocq --rocq-output-dir "$HERE" -o mips_tlb
sail "$LA_SRC" --rocq --rocq-output-dir "$HERE" -o loongarch_tlb
sail "$AA_SRC" --rocq --rocq-output-dir "$HERE" -o aarch64_tlb
sail "$SA_SRC" --rocq --rocq-output-dir "$HERE" -o sail_arm_tlb
sail "$INTC_SRC" --rocq --rocq-output-dir "$HERE" -o intc
sail "$TIMER_SRC" --rocq --rocq-output-dir "$HERE" -o timer

# Dev stdpp (9c7afbb6) lowered its singleton notations {[ x ]} / {[ k := a ]}
# to level 0, while Sail emits record-update notations
# {[ r 'with' field := e ]} at level 1; the two then have an incompatible
# prefix and {[ k := a ]} stops parsing.  Move the (unused) record-update
# notations to level 0 to restore coexistence with stdpp's singletons.
sed -i 's/\(Build_.*\)(at level 1)\./\1(at level 0)./' "$HERE/machine_types.v" "$HERE/mips_tlb_types.v" "$HERE/loongarch_tlb_types.v" "$HERE/aarch64_tlb_types.v" "$HERE/sail_arm_tlb_types.v" "$HERE/intc_types.v" "$HERE/timer_types.v"

# --- 4. compile the generated Rocq against SailStdpp + stdpp + iris ---
# (run from $HERE so machine.v can resolve `Require Import machine_types`)
cd "$HERE"
FLAGS="-Q $UC/stdpp stdpp -Q $UC/SailStdpp SailStdpp -Q $UC/iris iris"
rocq compile $FLAGS machine_types.v
rocq compile $FLAGS machine.v
rocq compile $FLAGS machine_encoding.v
rocq compile $FLAGS mword_lemmas.v
rocq compile $FLAGS coherence.v
rocq compile $FLAGS coherence_leaf.v
rocq compile $FLAGS tlb_tags.v
rocq compile $FLAGS mips_tlb_types.v
rocq compile $FLAGS mips_tlb.v
rocq compile $FLAGS mips_tlb_proofs.v
rocq compile $FLAGS mips_qemu_oracle.v
rocq compile $FLAGS loongarch_tlb_types.v
rocq compile $FLAGS loongarch_tlb.v
rocq compile $FLAGS loongarch_tlb_proofs.v
rocq compile $FLAGS loongarch_qemu_oracle.v
rocq compile $FLAGS aarch64_tlb_types.v
rocq compile $FLAGS aarch64_tlb.v
rocq compile $FLAGS aarch64_tlb_proofs.v
rocq compile $FLAGS sail_arm_tlb_types.v
rocq compile $FLAGS sail_arm_tlb.v
rocq compile $FLAGS aarch64_sail_oracle.v
rocq compile $FLAGS aarch64_pgcl.v
rocq compile $FLAGS pgcl_split.v
rocq compile $FLAGS shootdown.v
rocq compile $FLAGS machine_reify.v
rocq compile $FLAGS data_ram.v
rocq compile $FLAGS ipi.v
rocq compile $FLAGS intc_types.v
rocq compile $FLAGS intc.v
rocq compile $FLAGS intc_proofs.v
rocq compile $FLAGS intc_priority.v
rocq compile $FLAGS timer_types.v
rocq compile $FLAGS timer_ops.v
rocq compile $FLAGS timer_proofs.v
rocq compile $FLAGS conformance.v
rocq compile $FLAGS upstream_bridge.v
rocq compile $FLAGS bitfield_bridge.v
rocq compile $FLAGS iommu_conformance.v
rocq compile $FLAGS iommu_proofs.v
rocq compile $FLAGS cmdq_mmio.v
rocq compile $FLAGS vtd_proofs.v   # before reify: iommu_broadcast_reify imports it
rocq compile $FLAGS iommu_broadcast_reify.v
rocq compile $FLAGS smmu_proofs.v
rocq compile $FLAGS amdvi_proofs.v
rocq compile $FLAGS shootdown_iris.v

# --- 5. axiom hygiene: every headline theorem must be closed under the global
# context (no Axiom / Parameter / Admitted / admit). This is the machine-checked
# "axiom-free" claim, enforced on every build rather than by hand. ---
# The axiom-hygiene checks are independent of one another but each re-loads the
# module's .vo dependency graph, so they dominate the build wall-clock.  They are
# queued by `axiom_free` and drained in parallel by `axiom_free_drain` (bounded
# by $AXIOM_JOBS).  Each worker uses a unique temp .v in $HERE so sibling .vo
# files still resolve via the implicit loadpath, and reporting stays per-theorem.
# Set AXIOM_JOBS=1 to restore the old sequential behaviour.
AXIOM_JOBS="${AXIOM_JOBS:-8}"
_axiom_jobs="$(mktemp /tmp/axiom-jobs.XXXXXX)"
_axiom_worker="$(mktemp /tmp/axiom-worker.XXXXXX)"
trap 'rm -f "$_axiom_jobs" "$_axiom_worker" _axioms_*.v _axioms_*.vo _axioms_*.vos _axioms_*.vok _axioms_*.glob ._axioms_*.aux 2>/dev/null' EXIT

# The worker is a standalone script rather than an exported function: a heredoc
# inside an `export -f`-ed function is not reliably re-parsed by child shells
# (the positional-parameter expansion differs), so we write the script once and
# let xargs spawn it directly.  It uses `printf` (not a heredoc) to build the
# .v file, and $AXIOM_FLAGS (exported by axiom_free_drain) for the load path.
cat > "$_axiom_worker" <<'WORKER'
#!/usr/bin/env bash
set -euo pipefail
mod="$1"; thm="$2"; base="_axioms_${mod}_${thm}"
printf 'Require Import %s.\nPrint Assumptions %s.\n' "$mod" "$thm" > "$base.v"
if ! out="$(rocq compile $AXIOM_FLAGS "$base.v" 2>&1)"; then
  echo "CHECK FAILED: $mod.$thm did not compile:" >&2
  printf '%s\n' "$out" >&2
  rm -f "$base.v" "$base.vo" "$base.vos" "$base.vok" "$base.glob" ".$base.aux"
  exit 1
fi
rm -f "$base.v" "$base.vo" "$base.vos" "$base.vok" "$base.glob" ".$base.aux"
if printf '%s' "$out" | grep -q "Axioms:"; then
  echo "AXIOM LEAK: $mod.$thm is not axiom-free:" >&2
  printf '%s\n' "$out" >&2
  exit 1
fi
if ! printf '%s' "$out" | grep -q "Closed under the global context"; then
  echo "CHECK FAILED: could not confirm $mod.$thm is closed under the global context" >&2
  printf '%s\n' "$out" >&2
  exit 1
fi
echo "  axiom-free: $mod.$thm"
WORKER
chmod +x "$_axiom_worker"

axiom_free() { # $1 = module (no .v), $2 = theorem (queued; the flags are given at drain time)
  printf '%s %s\n' "$1" "$2" >> "$_axiom_jobs"
}

axiom_free_drain() { # $1 = flags to compile the queued checks with
  local flags="$1"
  [ -s "$_axiom_jobs" ] || return 0
  export AXIOM_FLAGS="$flags"
  if ! xargs -a "$_axiom_jobs" -n 2 -P "$AXIOM_JOBS" "$_axiom_worker"; then
    echo "AXIOM CHECK FAILURE (see above)" >&2
    : > "$_axiom_jobs"
    return 1
  fi
  : > "$_axiom_jobs"
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
# interrupt controller (SSG-3): the intc.sail device model reifies machine.sail's
# IPI mailbox — send latches pending, ack (pending & unmasked) rings the doorbell,
# and send+ack is exactly deliver_ipi's mailbox update.
axiom_free intc_proofs      intc_send_sets_pending
axiom_free intc_proofs      intc_send_preserves_ipi
axiom_free intc_proofs      intc_mask_sets_masked
axiom_free intc_proofs      intc_unmask_clears_masked
axiom_free intc_proofs      intc_ack_unmasked_clears_pending
axiom_free intc_proofs      intc_ack_unmasked_rings
axiom_free intc_proofs      intc_ack_masked_noop
axiom_free intc_proofs      intc_ack_no_pending_noop
axiom_free intc_proofs      intc_unmask_then_ack_delivers
axiom_free intc_proofs      intc_send_ack_refines_deliver_ipi
axiom_free intc_proofs      intc_delivery_enables_receive_ipi
axiom_free intc_proofs      test_vector_intc_send_ack_delivers
axiom_free intc_proofs      test_vector_intc_masked_holds
axiom_free intc_proofs      test_vector_intc_unmask_delivers
axiom_free intc_proofs      test_vector_intc_ack_clears_pending
# interrupt context (per-hart delivery gate): eidelivery / sstatus.SIE.  A hart
# in context holds its interrupt pending (no loss) and takes it only on exit.
axiom_free intc_proofs      intc_send_preserves_delivery
axiom_free intc_proofs      intc_mask_preserves_delivery
axiom_free intc_proofs      intc_unmask_preserves_delivery
axiom_free intc_proofs      intc_enter_context_clears_delivery
axiom_free intc_proofs      intc_exit_context_sets_delivery
axiom_free intc_proofs      intc_enter_context_preserves_pending
axiom_free intc_proofs      intc_enter_context_preserves_ipi
axiom_free intc_proofs      intc_ack_in_context_noop
axiom_free intc_proofs      test_vector_intc_context_holds
axiom_free intc_proofs      test_vector_intc_exit_delivers
# the "no lost or duplicated shootdown" composition: held in context (pending
# stays latched, doorbell silent), delivered exactly once on exit.
axiom_free intc_proofs      intc_exit_context_preserves_pending
axiom_free intc_proofs      intc_exit_context_preserves_ipi
axiom_free intc_proofs      intc_exit_context_preserves_masked
axiom_free intc_proofs      intc_enter_context_preserves_masked
axiom_free intc_proofs      intc_set_bit_length
axiom_free intc_proofs      intc_exit_then_ack_delivers
axiom_free intc_proofs      intc_no_lost_shootdown
axiom_free intc_proofs      test_vector_intc_context_holds_pending

# ---- timer (SSG-5) ----
axiom_free timer_proofs      timer_tick_mtime
axiom_free timer_proofs      timer_pending_after_ack
axiom_free timer_proofs      timer_set_mtimecmp_other
axiom_free timer_proofs      timer_set_mtimecmp_mtime_unchanged
axiom_free timer_proofs      build_harts_length
axiom_free timer_proofs      test_vec_init_mtime
axiom_free timer_proofs      test_vec_init_pending_hart0
axiom_free timer_proofs      test_vec_tick_increases
axiom_free timer_proofs      test_vec_set_cmp_then_tick
axiom_free timer_proofs      test_vec_ack_clears
# intc -> S2.4 bridge: the controller's send+ack realizes the weak-memory
# broadcast's deliver_ipi ghost step (delivery precedes ack via the device).
axiom_free intc_proofs      intc_receive_ipi_eq_deliver
axiom_free intc_proofs      intc_receive_ipi_cores_eq_deliver
axiom_free intc_proofs      test_vector_intc_receive_ipi_eq_deliver
# interrupt priority selection (`*topei` / ICC_IAR): the least eligible identity
# (lowest identity number = highest priority), threshold via `eithreshold`.
axiom_free intc_priority    topei_some_eligible
axiom_free intc_priority    topei_minimal
axiom_free intc_priority    topei_none_no_eligible
axiom_free intc_priority    topei_priority
axiom_free intc_priority    test_vector_topei_highest_priority
axiom_free intc_priority    test_vector_topei_skips_disabled
axiom_free intc_priority    test_vector_topei_threshold
axiom_free intc_priority    test_vector_topei_threshold_masks_all
axiom_free intc_priority    test_vector_topei_none
axiom_free conformance      translate_conforms
axiom_free conformance      test_vector_mapping_ok
axiom_free conformance      test_vector_writeonly_faults
axiom_free conformance      test_vector_writeonly_exec_faults
axiom_free conformance      test_vector_missing_pte_faults
axiom_free conformance      test_vector_superpage_faults
axiom_free conformance      test_vector_execonly
axiom_free conformance      test_vector_writeonly_conforms
axiom_free conformance      test_vector_napot_mapping
axiom_free conformance      test_vector_napot_bad_faults
axiom_free conformance      test_vector_napot_conforms
axiom_free conformance      test_vector_napot_bad_conforms
axiom_free conformance      test_vector_napot_nonleaf_faults
axiom_free conformance      test_vector_napot_nonleaf_conforms
axiom_free conformance      walk_decision_fault_iff_upstream_invalid
axiom_free conformance      walk_decision_pointer_iff_upstream_non_leaf
# G1 upstream-bridge: the shared `walk_decision` agrees with the *verbatim
# upstream* sail-riscv PTE predicates (pte_is_invalid / pte_is_non_leaf),
# mechanically generated from machine.sail — the bridge lemma set of
# doc/trust-line-plan.md Step 4.1.
axiom_free upstream_bridge  walk_decision_fault_iff
axiom_free upstream_bridge  walk_decision_pointer_iff
axiom_free upstream_bridge  walk_decision_leaf_iff
axiom_free upstream_bridge  walk_decision_napot_iff
axiom_free upstream_bridge  bridge_vec_invalid_v0
axiom_free upstream_bridge  bridge_vec_writeonly
axiom_free upstream_bridge  bridge_vec_pointer
axiom_free upstream_bridge  bridge_vec_pointer_napot
axiom_free upstream_bridge  bridge_vec_leaf
axiom_free upstream_bridge  bridge_vec_napot
axiom_free upstream_bridge  bridge_vec_superpage_not_invalid
axiom_free upstream_bridge  bridge_vec_superpage_faults
# G1 PTE-flags bridge (bitfield_bridge.v): the flag extraction from a bits(64)
# PTE word agrees with the structured Pte record fields — per-field vectors on
# concrete Sv39 PTE words + flag roundtrip on an encoded Pte (encoding then
# decoding recovers the boolean fields).  Seven concrete words cover every flag
# combination (ro/ptr/invalid/writeonly/rw/exec-only/napot).
axiom_free bitfield_bridge vec_ro_valid
axiom_free bitfield_bridge vec_ro_read
axiom_free bitfield_bridge vec_ro_write
axiom_free bitfield_bridge vec_ro_exec
axiom_free bitfield_bridge vec_ro_user
axiom_free bitfield_bridge vec_ro_napot
axiom_free bitfield_bridge vec_ptr_valid
axiom_free bitfield_bridge vec_ptr_read
axiom_free bitfield_bridge vec_ptr_napot
axiom_free bitfield_bridge vec_inv_valid
axiom_free bitfield_bridge vec_wo_valid
axiom_free bitfield_bridge vec_wo_read
axiom_free bitfield_bridge vec_wo_write
axiom_free bitfield_bridge vec_wo_exec
axiom_free bitfield_bridge vec_wo_upstream_invalid
axiom_free bitfield_bridge vec_rw_valid
axiom_free bitfield_bridge vec_rw_read
axiom_free bitfield_bridge vec_rw_write
axiom_free bitfield_bridge vec_xo_valid
axiom_free bitfield_bridge vec_xo_read
axiom_free bitfield_bridge vec_xo_exec
axiom_free bitfield_bridge vec_napot_valid
axiom_free bitfield_bridge vec_napot_napot
axiom_free bitfield_bridge roundtrip_valid
axiom_free bitfield_bridge roundtrip_read
axiom_free bitfield_bridge roundtrip_write
axiom_free bitfield_bridge roundtrip_exec
axiom_free bitfield_bridge roundtrip_user
axiom_free bitfield_bridge roundtrip_napot
# IOMMU (SSG-4) conformance cross-check: the walker is translate re-rooted (so
# G1's upstream-oracle agreement transfers), and the invalidation is pinned per
# platform (VT-d IOTLB Invalidate §6.5.2.3 / SMMU TLBI §4.4 /
# AMD-Vi INVALIDATE_IOMMU_PAGES §2.4.3).
axiom_free iommu_conformance iommu_walk_conforms
axiom_free iommu_conformance iommu_walk_translate_conforms
axiom_free iommu_conformance test_vector_vtd_iotlb_invalidate
axiom_free iommu_conformance test_vector_smmu_iotlb_invalidate
axiom_free iommu_conformance test_vector_amdvi_iotlb_invalidate_noop
# ATS/PRI device side vs PCIe 6.0: the translation completion is the walk's,
# and a page request is serviced at most once per (Requestor ID, PASID,
# address), with the pending-bit retry loop (Set while unresolved, Clear once
# the kernel mapped the page) and the fault-message payload naming the endpoint.
axiom_free iommu_conformance test_vector_pcie_ats_completion
axiom_free iommu_conformance test_vector_pcie_pri_at_most_once
axiom_free iommu_conformance test_vector_pcie_pri_retry_cycle
axiom_free iommu_conformance test_vector_pcie_pri_fault_delivers
axiom_free iommu_conformance test_vector_amdvi_invalidate_iotlb_all
axiom_free iommu_conformance test_vector_smmu_invalidate_devtlb_all
axiom_free iommu_conformance test_vector_smmu_tlbi_asid
axiom_free iommu_conformance test_vector_amdvi_invalidate_domain
axiom_free iommu_conformance test_vector_smmu_tlbi_asid_noop
axiom_free iommu_conformance test_vector_amdvi_invalidate_domain_noop
# VT-d P_IOTLB PASID-selective vectors (§6.5.2.4): the (DID, PASID) granularity
# on the mixed IOTLB (removes exactly the associated entry), the absent-tag
# no-op, and the idempotent re-issue of the IOTLB half of the §6.5.2.2 pairing.
axiom_free iommu_conformance test_vector_vtd_piotlb_pasid_selective
axiom_free iommu_conformance test_vector_vtd_piotlb_pasid_selective_noop
axiom_free iommu_conformance test_vector_vtd_piotlb_pair_iotlb_half
# The composed VA+tag granules (granularity-matrix replay of the VT-d PASID-
# cache work): SMMU TLBI_VA_ASID and AMD-Vi INVALIDATE_IOMMU_PAGES-by-(domain,
# VA), plus the device-TLB domain invalidation (AMD-Vi INVALIDATE_DEVTBL-SEL).
axiom_free iommu_conformance test_vector_smmu_tlbi_va_asid
axiom_free iommu_conformance test_vector_amdvi_invalidate_pages_domain_va
axiom_free iommu_conformance test_vector_amdvi_invalidate_devtbl_domain
# the descriptor-acceptance matrix (VT-d 5.20 §6.5.2.3/§6.5.2.4): the
# granularity-validity vectors pin the reserved encodings — 10b on the
# PASID-cache invalidation, 00b/01b on the P_IOTLB — as invalid descriptors,
# and the queued P_IOTLB pairing vector.
axiom_free iommu_conformance test_vector_granularity_valid_pasid_cache
axiom_free iommu_conformance test_vector_granularity_valid_p_iotlb
axiom_free iommu_conformance test_vector_granularity_valid_reserved_10b
axiom_free iommu_conformance test_vector_iommu_queue_piotlb_pair
# Intel VT-d S4.5 first slice: Requester-ID context selection and the
# second-level walk, with explicit missing/non-present faults and oracle replay.
axiom_free vtd_proofs vtd_walk_context_spec
axiom_free vtd_proofs vtd_walk_missing_context
axiom_free vtd_proofs vtd_walk_nonpresent_context
axiom_free vtd_proofs vtd_walk_conforms
axiom_free vtd_proofs test_vector_vtd_context_hit
axiom_free vtd_proofs test_vector_vtd_nonpresent_fault
axiom_free vtd_proofs test_vector_vtd_missing_context_fault
axiom_free vtd_proofs test_vector_vtd_context_walk_fault
# S4.5 first-stage / PASID slice: the two-stage (GVA->GPA->SPA) walk and its
# per-stage fault/hit specs, the structural faults, and the conformance oracle
# (VT-d 5.20 §3 / §15).
axiom_free vtd_proofs vtd_walk_pasid_two_stage
axiom_free vtd_proofs vtd_walk_pasid_missing_context
axiom_free vtd_proofs vtd_walk_pasid_nonpresent_context
axiom_free vtd_proofs vtd_walk_pasid_missing_pasid_entry
axiom_free vtd_proofs vtd_walk_pasid_nonpresent_pasid_entry
axiom_free vtd_proofs vtd_walk_pasid_stage1_faults
axiom_free vtd_proofs vtd_walk_pasid_stage2_faults
axiom_free vtd_proofs vtd_walk_pasid_spec
axiom_free vtd_proofs vtd_walk_pasid_conforms
axiom_free vtd_proofs test_vector_vtd_pasid_two_stage_hit
axiom_free vtd_proofs test_vector_vtd_pasid_missing_fault
axiom_free vtd_proofs test_vector_vtd_pasid_nonpresent_fault
axiom_free vtd_proofs test_vector_vtd_pasid_nonpresent_context_fault
axiom_free vtd_proofs test_vector_vtd_pasid_empty_fault
# S4.5 PASID-cache slice: the cached first-stage lookup is an alias of the
# PASID table, so the cached two-stage walk equals the table-driven one.
axiom_free vtd_proofs pasid_cached_walk_two_stage
axiom_free vtd_proofs pasid_cached_walk_of_table
axiom_free vtd_proofs pasid_cached_walk_coherent
axiom_free vtd_proofs test_vector_vtd_pasid_cache_coherent
# S4.5 fault-recording slice: a record (DID, PASID, IOVA, reason) is produced
# exactly when the two-stage walk faults.
axiom_free vtd_proofs vtd_record_fault_stage1_spec
axiom_free vtd_proofs vtd_record_fault_stage2_spec
axiom_free vtd_proofs vtd_record_fault_hit_none
axiom_free vtd_proofs vtd_record_fault_iff_walk
axiom_free vtd_proofs test_vector_vtd_record_fault_stage1
axiom_free vtd_proofs test_vector_vtd_record_fault_missing_context
axiom_free vtd_proofs test_vector_vtd_record_fault_hit_none
# S4.5 PASID in the machine ghost: after the queue shootdown un-maps the freed
# frame at the context's SL root, the two-stage PASID walk faults and a fault is
# recorded — the functional precondition the weak-memory ghost's post-state
# (iommu_shootdown_via_queue) satisfies.
axiom_free vtd_proofs vtd_shootdown_via_queue_pasid_faults
axiom_free vtd_proofs test_vector_vtd_shootdown_pasid
axiom_free vtd_proofs test_vector_vtd_shootdown_pasid_record
# S4.5 PASID-cache eviction / refill: eviction breaks the cached walk for a
# PASID (a miss), refill with the table root restores coherence — the
# invalidation-then-retranslate cycle.
# S4.5 PASID-cache tags (DID+PASID) + eviction / refill: the cache is tagged
# by (DID, PASID), so the lookup scans by tag equality, eviction clears every
# entry of a DID (device-selective invalidation), and refill re-installs the
# table's root under the full tag — the miss/refill cycle a translation after
# invalidation must go through.
axiom_free vtd_proofs pasid_cache_lookup_tagged
axiom_free vtd_proofs pasid_cache_evict_lookup
axiom_free vtd_proofs pasid_cached_walk_evict_misses
axiom_free vtd_proofs pasid_cache_evict_preserves_other_did
axiom_free vtd_proofs pasid_cache_refill_lookup
axiom_free vtd_proofs pasid_cache_refill_fresh
axiom_free vtd_proofs pasid_cache_refill_coherent
axiom_free vtd_proofs pasid_cache_evict_refill_cycle
axiom_free vtd_proofs test_vector_vtd_pasid_cache_evict
axiom_free vtd_proofs test_vector_vtd_pasid_cache_tags
# S4.5 scalable-mode device table: the DTE-selected context walk reduces to
# the context's SL walk and agrees with the flat vtd_walk when the DTE points
# at the context the flat lookup finds; each structural fault is covered.
axiom_free vtd_proofs vtd_walk_device_two_stage
axiom_free vtd_proofs vtd_walk_device_of_context
axiom_free vtd_proofs vtd_walk_device_missing_fault
axiom_free vtd_proofs vtd_walk_device_nonpresent_fault
axiom_free vtd_proofs vtd_walk_device_missing_context_fault
axiom_free vtd_proofs vtd_walk_device_nonpresent_context_fault
axiom_free vtd_proofs test_vector_vtd_walk_device_hit
# S4.5 FRCD + fault-message signalling: a fault is recorded as an FRCD entry,
# the FRCD raises the interrupt line, and the message carries (DID, PASID).
axiom_free vtd_proofs frcd_record_adds
axiom_free vtd_proofs frcd_record_preserves
axiom_free vtd_proofs frcd_record_signals
axiom_free vtd_proofs fault_msg_of_record
axiom_free vtd_proofs vtd_shootdown_frcd_pending
# S4.5 FRCDR drain-by-software: read the head, clear, drain — the line
# deasserts and the interrupt controller sees a no-op.
axiom_free vtd_proofs frcd_head_record
axiom_free vtd_proofs frcd_clear_deasserts
axiom_free vtd_proofs frcd_drain_clears
axiom_free vtd_proofs frcd_drain_deasserts
axiom_free vtd_proofs frcd_drain_recovers
axiom_free vtd_proofs frcd_drain_cycle
axiom_free vtd_proofs test_vector_frcd_drain
axiom_free vtd_proofs test_vector_vtd_frcd_pending
# S4.5 PASID in-loop translation with fill-on-miss: the loop recovers from an
# eviction by re-walking the table and refilling (the translate-then-refill cycle).
axiom_free vtd_proofs pasid_translate_fill_hit
axiom_free vtd_proofs pasid_translate_fill_miss_refills
axiom_free vtd_proofs pasid_translate_fill_miss_missing_table
axiom_free vtd_proofs pasid_translate_fill_miss_nonpresent_table
axiom_free vtd_proofs pasid_translate_fill_after_evict
# S4.5 in-loop fill-on-miss under the full tag: the refilled entry carries the
# (DID, PASID) tag with the table's root, and after an eviction the loop
# recovers to a *coherent* cache answering with the table result.
axiom_free vtd_proofs pasid_translate_fill_refill_tagged
axiom_free vtd_proofs pasid_translate_fill_after_evict_refilled_coherent
axiom_free vtd_proofs test_vector_pasid_translate_fill_after_evict
# S4.5 FRCD interrupt delivery into the core INTC: a pending FRCD raises the
# fault line (latched), the ack rings the doorbell — the SSG-3 tie-in.
axiom_free vtd_proofs frcd_signal_raises
axiom_free vtd_proofs frcd_signal_drained_noop
axiom_free vtd_proofs vtd_shootdown_frcd_delivers
axiom_free vtd_proofs vtd_fault_ack_rings
axiom_free vtd_proofs test_vector_vtd_frcd_delivers
axiom_free vtd_proofs test_vector_vtd_frcd_ack_rings
# S4.5 DTE PASID-table pointers: the scalable-mode two-stage walk (DTE ->
# PASID table -> first stage, then the selected context's second level) and
# its agreement with the flat vtd_walk_pasid.
axiom_free vtd_proofs vtd_walk_device_pasid_two_stage
axiom_free vtd_proofs vtd_walk_device_pasid_of_flat
axiom_free vtd_proofs vtd_walk_device_pasid_missing_fault
axiom_free vtd_proofs vtd_walk_device_pasid_nonpresent_fault
axiom_free vtd_proofs vtd_walk_device_pasid_missing_table_fault
axiom_free vtd_proofs vtd_walk_device_pasid_missing_entry_fault
axiom_free vtd_proofs vtd_walk_device_pasid_nonpresent_entry_fault
axiom_free vtd_proofs test_vector_vtd_walk_device_pasid_hit
# S4.5 PASID-cache invalidation granularity (VT-d 5.20 §6.5.2.4): PASID-
# selective clears exactly the (did, pasid) tag, global clears everything, and
# the evict -> refill cycle restores the table-driven cached walk.
axiom_free vtd_proofs pasid_cache_evict_pasid_clears
axiom_free vtd_proofs pasid_cache_evict_all_clears
axiom_free vtd_proofs pasid_cache_evict_pasid_preserves_other
axiom_free vtd_proofs pasid_cache_evict_pasid_refill_cycle
axiom_free vtd_proofs test_vector_vtd_pasid_cache_granularity
# S4.5 PASID-cache generation tags (VT-d 5.20 §15.4): the (DID, PASID,
# generation) tag — a stale generation never answers the current-generation
# lookup, the reuse is detected as a tag conflict, evicted, and refilled
# under the current generation, after which no conflict remains.
axiom_free vtd_proofs pasid_cache_lookup_gen_installs
axiom_free vtd_proofs pasid_cache_lookup_gen_stale_singleton
axiom_free vtd_proofs pasid_cache_evict_gen_clears_present
axiom_free vtd_proofs pasid_cache_evict_gen_preserves_fresh
axiom_free vtd_proofs pasid_cache_evict_gen_preserves_other_did
axiom_free vtd_proofs pasid_cache_evict_gen_conflict_free
axiom_free vtd_proofs pasid_cache_refill_gen_conflict_free
axiom_free vtd_proofs pasid_cache_evict_gen_refill_cycle
axiom_free vtd_proofs test_vector_pasid_cache_generation
# S4.5 VT-d PASID generation-tagged fill-on-miss loop (VT-d §6.2.3 /
# §6.5.2.2): a current-generation hit is served from the cache, a stale or
# absent generation re-walks the PASID table and refills under g, and the
# post-eviction path has the same result; the executable vector is also the
# spec-boundary cross-check.
axiom_free vtd_proofs pasid_translate_fill_gen_hit
axiom_free vtd_proofs pasid_translate_fill_gen_miss_refills
axiom_free vtd_proofs pasid_translate_fill_gen_after_evict
axiom_free vtd_proofs test_vector_pasid_translate_fill_generation
# S4.5 device-table fill-on-miss: the translation service loop *over the
# device table* — hit walks the cached root (keyed by the DTE's DID), miss
# re-walks the device's PASID table, refills under (d.did, pasid), and after
# an eviction of the DTE's DID the loop recovers to the device-table walk.
axiom_free vtd_proofs vtd_device_translate_fill_hit
axiom_free vtd_proofs vtd_device_translate_fill_miss_refills
axiom_free vtd_proofs vtd_device_translate_fill_miss_missing_table
axiom_free vtd_proofs vtd_device_translate_fill_miss_nonpresent_entry
axiom_free vtd_proofs vtd_device_translate_fill_after_evict
axiom_free vtd_proofs vtd_device_translate_fill_refill_tagged
axiom_free vtd_proofs test_vector_vtd_device_translate_fill_hit
axiom_free vtd_proofs test_vector_vtd_device_translate_fill_after_evict
# S4.5 PRI x FRCD composition: a pending page request's translation fault
# records into the FRCD (raising the fault-message interrupt with the
# (did, pasid) payload); resolving the request makes the path silent.
axiom_free vtd_proofs pri_fault_frcd_records
axiom_free vtd_proofs pri_fault_frcd_after_resolve_silent
axiom_free vtd_proofs test_vector_pri_fault_frcd
# S4.5 PRI fault -> INTC delivery: the pending-bit twin of the shootdown-
# driven chain — fault record -> FRCD -> line raised on the target core, the
# ack rings the doorbell, and a resolved request is silent.
axiom_free vtd_proofs pri_fault_frcd_delivers_intc
axiom_free vtd_proofs pri_fault_frcd_ack_rings
axiom_free vtd_proofs pri_fault_frcd_resolved_silent
axiom_free vtd_proofs test_vector_pri_fault_frcd_delivers_intc
# IOMMU (SSG-4 / S4.1b): the IOTLB coherence replay — invalidate drops the
# unmapped page's entries, the walk faults, and unmap+invalidate keeps the device
# from reaching the freed frame (vs the stale-entry bug when invalidate is omitted).
axiom_free iommu_proofs      iotlb_invalidate_removes
axiom_free iommu_proofs      iommu_unmap_faults
axiom_free iommu_proofs      iommu_unmap_correct
axiom_free iommu_proofs      iommu_unmap_without_invalidate_breaks
axiom_free iommu_proofs      test_vector_iommu_invalidate_va0
axiom_free iommu_proofs      test_vector_iommu_invalidate_va4096
axiom_free iommu_proofs      test_vector_iommu_walk_empty_faults
# IOMMU (SSG-4 / S4.1c): pte_address injectivity — the deferred "arithmetic
# opaque" boundary, now closed.  pte_address packs the PPN into bits [55:12] and
# the index into [11:3], so equal slot addresses have equal PPN and index, and
# distinct indices yield distinct slot addresses (the ingredient the universal
# `IOTLB ⊆ mapping` invariant needs).
axiom_free iommu_proofs      mword_uint_inj
axiom_free iommu_proofs      mword_uint_range
axiom_free iommu_proofs      uint_lt_pow2
axiom_free iommu_proofs      pow2_56_gt_12
axiom_free iommu_proofs      pow2_56_gt_3
axiom_free iommu_proofs      uint_pte_address
axiom_free iommu_proofs      low12_of_pte_address
axiom_free iommu_proofs      pte_address_injective
axiom_free iommu_proofs      pte_address_neq_index
# S4.1c (universal-invariant infrastructure): the frame lemma `translate_remove_frame`
# (removing a slot leaves an unrelated walk untouched — the reduction the literal
# `IOTLB ⊆ mapping` invariant needs) and the `read_pte -> In` bridge to the
# `wf_page_table` forest condition.  `is_table`/`wf_page_table`/`iotlb_coherent` are
# transparent Definitions, so not axiom-checked; the headline preservation theorem
# is deferred on the pure `vpn_of = concat(vpn2,vpn1,vpn0)` lemma (S4.1d).
axiom_free iommu_proofs      read_pte_Some_In
axiom_free iommu_proofs      translate_remove_frame
# IOMMU (SSG-4 / S4.1d): the literal `IOTLB ⊆ mapping` invariant is preserved by
# unmap+invalidate.  The bitvector reconstruction (`vpn_of` is determined by its
# three 9-bit levels) plus the forest/injectivity case analysis closes the last
# deferred arithmetic boundary.
axiom_free iommu_proofs      vpn_bits_reconstruct
axiom_free iommu_proofs      vpn_of_determined
axiom_free iommu_proofs      leaf_addr_spec
axiom_free iommu_proofs      pte_address_ppn_neq
axiom_free iommu_proofs      iotlb_invalidate_In
axiom_free iommu_proofs      unmap_slot_neq_root_slot
axiom_free iommu_proofs      unmap_slot_neq_level1_slot
axiom_free iommu_proofs      unmap_slot_neq_level0_slot
axiom_free iommu_proofs      iommu_unmap_preserves_coherence
# IOMMU (SSG-4 / S4.3): ATS/PRI device-side model — the translation request →
# completion fills the IOTLB + device-TLB, the per-device invalidation, and the
# page-request dedup (at most one pending per (did, iova)).
axiom_free iommu_proofs      test_vector_ats_translate_hit
axiom_free iommu_proofs      test_vector_ats_translate_fault
axiom_free iommu_proofs      test_vector_ats_invalidate
axiom_free iommu_proofs      test_vector_pri_request_enqueue
axiom_free iommu_proofs      test_vector_pri_request_dedup
# S4.3 ATS/PRI proofs (beyond the vectors): the completion is exactly the walk's
# result, a fault caches nothing, the device-TLB invalidation drops the unmapped
# page, and PRI dedups (a page request is serviced at most once per (did,iova)).
axiom_free iommu_proofs      ats_translate_spec
axiom_free iommu_proofs      ats_translate_fault
axiom_free iommu_proofs      ats_invalidate_removes
# S4.3 ATS/PRI fault path (PCIe ATS §4.2 / VT-d 5.20 §7.2, §10.4.14): the
# (did, pasid, iova)-tagged page request re-pends on re-issue, the pending-bit
# recheck observes the resolution once the kernel maps the page, and a pending
# request's translation fault delivers the fault record (the FRCD composition
# lives in vtd_proofs.v).
axiom_free iommu_proofs      pri_request_repends
axiom_free iommu_proofs      pri_pending_enqueue
axiom_free iommu_proofs      pri_resolve_clears
axiom_free iommu_proofs      pri_retry_cycle
axiom_free iommu_proofs      pri_fault_delivers_pending
axiom_free iommu_proofs      pri_fault_delivers_none
# IOMMU (SSG-4 / S4.2a): the functional IOMMU broadcast shootdown — break-before-
# make + IOTLB invalidate + IPI-delivered CPU-TLB flush, refining the CPU-side
# `invalidate_shootdown` and dropping the unmapped page's device translations.
axiom_free iommu_proofs      iommu_invalidate_faults
axiom_free iommu_proofs      ipi_broadcast_cores_preserves_iotlb
axiom_free iommu_proofs      iommu_shootdown_iotlb
axiom_free iommu_proofs      iommu_shootdown_refines_invalidate_shootdown
axiom_free iommu_proofs      iommu_shootdown_correct
axiom_free iommu_proofs      test_vector_iommu_shootdown
# IOMMU (SSG-4 / S4.2b-1): the queued-invalidation formulation of the broadcast.
# unmap -> enqueue Invalidate+Wait -> drain (iommu_process_queue) => the device
# walk faults and no stale IOTLB entry survives (the command-queue twin of
# iommu_shootdown_correct).
axiom_free iommu_proofs      iommu_process_queue_spec
axiom_free iommu_proofs      iommu_shootdown_via_queue_mem
axiom_free iommu_proofs      iommu_shootdown_via_queue_iotlb
axiom_free iommu_proofs      iommu_shootdown_via_queue_correct
axiom_free iommu_proofs      test_vector_iommu_process_queue
# IOMMU (SSG-4 / S4.2b-3): the ATS device-TLB tier — the full shootdown also
# invalidates each endpoint's device-TLB, so after it no CPU TLB, no IOTLB, and
# no device-TLB entry translates the freed frame.
axiom_free iommu_proofs      iommu_shootdown_ats_mem
axiom_free iommu_proofs      iommu_shootdown_ats_cores
axiom_free iommu_proofs      iommu_shootdown_ats_iotlb
axiom_free iommu_proofs      iommu_shootdown_ats_devtlbs
axiom_free iommu_proofs      iommu_shootdown_ats_correct
# device-TLB lookup (S4.2b-3 strengthening): find_devtlb faults for the freed
# frame after the ATS invalidation — the concrete "no device translates the
# freed frame" claim.
axiom_free iommu_proofs      find_devtlb_none_of_forall
axiom_free iommu_proofs      find_devtlb_after_ats_invalidate
axiom_free iommu_proofs      iommu_shootdown_ats_devtlb_faults
# ALL-granularity invalidation (AMD-Vi §2.4.8 / SMMU TLBI_ALL): the second
# invalidation shape — clear every cached translation.
axiom_free iommu_proofs      iotlb_invalidate_all_clears
axiom_free iommu_proofs      ats_invalidate_all_clears
axiom_free iommu_proofs      find_devtlb_after_ats_invalidate_all
axiom_free iommu_proofs      iotlb_invalidate_pasid_removes
axiom_free iommu_proofs      iotlb_invalidate_domain_removes
# VT-d P_IOTLB PASID-selective (S4.5 cross-check, §6.5.2.4): the (DID, PASID)
# granularity drops entries associated with both tags, and the mandatory
# §6.5.2.2 pairing — a PASID-selective-within-domain PASID-cache invalidation
# (01b) followed by a PASID-selective P_IOTLB (10b) — clears the tag from the
# cache (no present entry) and from the IOTLB (no entry at all).
axiom_free iommu_proofs      iotlb_invalidate_pasid_did_removes
axiom_free iommu_proofs      iotlb_pasid_cache_pair_invalidate_clears
# The composed VA+tag granules (SMMU TLBI_VA_ASID / AMD-Vi pages-by-(domain,
# VA)) remove the intersection, and the device-TLB domain invalidation
# (AMD-Vi INVALIDATE_DEVTBL-SEL) drops the domain's entries.
axiom_free iommu_proofs      iotlb_invalidate_va_asid_removes
axiom_free iommu_proofs      iotlb_invalidate_domain_va_removes
axiom_free iommu_proofs      ats_invalidate_domain_removes
axiom_free iommu_proofs      find_devtlb_after_ats_invalidate_domain
# command-queue MMIO (SSG-4 / S4.2c): the head/tail (prod/cons) registers are
# pure bookkeeping — the MMIO drain realizes iommu_process_queue.
axiom_free cmdq_mmio         cmdq_drain_refines_iommu_process_queue
axiom_free cmdq_mmio         cmdq_drain_invalidate_wait_spec
axiom_free cmdq_mmio         test_vector_cmdq_mmio_drain
# IOMMU (SSG-4 / S4.2b-2 reification): the composition's MMIO drain ghost step
# produces exactly iommu_shootdown_via_queue's invalidated IOTLB, and the freed
# frame faults / no stale IOTLB entry survives (iommu_shootdown_via_queue_correct).
axiom_free iommu_broadcast_reify iommu_drain_iotlb_reifies
axiom_free iommu_broadcast_reify iommu_broadcast_reifies_correct
axiom_free iommu_broadcast_reify test_vector_iommu_broadcast_reifies
# S4.5 the drain's VT-d meaning: the MMIO drain makes the two-stage PASID walk
# fault and records the fault (the ghost post-state's VT-d precondition).
axiom_free iommu_broadcast_reify vtd_broadcast_reifies_pasid
axiom_free iommu_broadcast_reify test_vector_vtd_broadcast_reifies_pasid
# SMMUv3 two-stage walk (SSG-4 / S4.4): the composition is GVA → GPA → SPA —
# faults iff either stage faults, and a two-stage hit returns the stage-2
# (SPA, perm).
axiom_free smmu_proofs        smmu_walk_stage1_faults
axiom_free smmu_proofs        smmu_walk_stage2_faults
axiom_free smmu_proofs        smmu_walk_spec
axiom_free smmu_proofs        test_vector_smmu_two_stage_empty_faults
axiom_free smmu_proofs        smmu_unmap_stage1_faults
axiom_free smmu_proofs        smmu_unmap_stage2_faults
axiom_free smmu_proofs        smmu_translate_spec
axiom_free smmu_proofs        smmu_translate_faults_missing_ste
axiom_free smmu_proofs        smmu_translate_faults_invalid_ste
axiom_free smmu_proofs        smmu_translate_faults_invalid_cd
axiom_free smmu_proofs        test_vector_smmu_translate_empty_stes
axiom_free smmu_proofs        test_vector_smmu_translate_hit_empty_walk
axiom_free smmu_proofs        test_vector_smmu_two_stage_hit
axiom_free smmu_proofs        test_vector_smmu_translate_hit
axiom_free smmu_proofs        smmu_shootdown_iotlb
axiom_free smmu_proofs        smmu_shootdown_stage1_correct
axiom_free smmu_proofs        smmu_shootdown_stage2_correct
axiom_free smmu_proofs        smmu_walk_conforms
axiom_free smmu_proofs        smmu_translate_conforms
# S4.5 SMMU walker replay of the fill-on-miss loop (IOTLB hit / miss-refill /
# invalidate-then-retranslate).
axiom_free smmu_proofs        smmu_translate_fill_hit
axiom_free smmu_proofs        smmu_translate_fill_miss_refills
axiom_free smmu_proofs        smmu_translate_fill_after_invalidate
axiom_free smmu_proofs        test_vector_smmu_translate_fill_hit
axiom_free smmu_proofs        test_vector_smmu_translate_fill_miss
axiom_free smmu_proofs        test_vector_smmu_translate_fill_after_invalidate
# AMD-Vi 4-level I/O page-table walk (SSG-4 / S4.4): level-3 resolves to a
# non-leaf PTE, then the bottom 3 levels are translate re-rooted there — the
# 4-level walk subsumes the 3-level walk.
axiom_free amdvi_proofs        amdvi_walk_refines_iommu_walk
axiom_free amdvi_proofs        amdvi_walk_level3_faults
axiom_free amdvi_proofs        test_vector_amdvi_4level_empty_faults
axiom_free amdvi_proofs        test_vector_amdvi_4level_hit
axiom_free amdvi_proofs        test_vector_amdvi_4level_invalid_l3
axiom_free amdvi_proofs        test_vector_amdvi_4level_leaf_l3
axiom_free amdvi_proofs        test_vector_amdvi_4level_napot_l3
axiom_free amdvi_proofs        amdvi_unmap_faults
axiom_free amdvi_proofs        amdvi_unmap_correct
axiom_free amdvi_proofs        amdvi_walk_conforms
# S4.5 AMD-Vi walker replay of the fill-on-miss loop (miss-refill /
# INVALIDATE_IOMMU_PAGES invalidate-then-retranslate).
axiom_free amdvi_proofs        amdvi_translate_fill_miss_refills
axiom_free amdvi_proofs        amdvi_translate_fill_after_invalidate
axiom_free amdvi_proofs        test_vector_amdvi_translate_fill_miss
axiom_free amdvi_proofs        test_vector_amdvi_translate_fill_after_invalidate
# IOMMU (SSG-4 / S4.2b-2 groundwork): the queue drain reifies the functional
# broadcast — iommu_shootdown_via_queue and iommu_shootdown agree on mem and
# IOTLB (the pure precondition the weak-memory lift must satisfy).
axiom_free iommu_proofs      iotlb_lookup_after_invalidate
# S4.5 gen-tag replay on the IOTLB: the generation-tagged view of the walker
# loops (lookup_gen answers current generations, stale generations miss,
# evict_gen clears the stale-tag conflict, refill_gen installs the fresh one,
# and the evict-then-refill cycle ends conflict-free).
axiom_free iommu_proofs      iotlb_lookup_gen_Some_implies
axiom_free iommu_proofs      iotlb_lookup_gen_stale_misses
axiom_free iommu_proofs      iotlb_tag_conflict_stale_exists
axiom_free iommu_proofs      iotlb_evict_gen_clears_conflict
axiom_free iommu_proofs      iotlb_lookup_gen_after_evict_gen_same_g
axiom_free iommu_proofs      iotlb_lookup_gen_after_refill_gen
axiom_free iommu_proofs      iotlb_tag_conflict_after_refill_gen
axiom_free iommu_proofs      iotlb_evict_gen_refill_cycle
axiom_free iommu_proofs      iotlb_lookup_gen_after_invalidate
# S4.5 gen-tag replay on the SMMU/AMD-Vi walker loops: the generation-tagged
# fill-on-miss loops (smmu_translate_fill_gen / amdvi_translate_fill_gen) —
# a gen-g hit answers from the cache, a gen-g miss re-walks and refills under
# g, and after a 4KiB TLBI / INVALIDATE_IOMMU_PAGES the gen-g lookup misses
# (no entry survives at any generation) so the loop recovers by refilling
# under g.
axiom_free smmu_proofs      smmu_translate_fill_gen_hit
axiom_free smmu_proofs      smmu_translate_fill_gen_miss_refills
axiom_free smmu_proofs      smmu_translate_fill_gen_after_invalidate
axiom_free smmu_proofs      test_vector_smmu_translate_fill_gen_miss
axiom_free smmu_proofs      test_vector_smmu_translate_fill_gen_after_invalidate
axiom_free amdvi_proofs     amdvi_translate_fill_gen_hit
axiom_free amdvi_proofs     amdvi_translate_fill_gen_miss_refills
axiom_free amdvi_proofs     amdvi_translate_fill_gen_after_invalidate
axiom_free amdvi_proofs     test_vector_amdvi_translate_fill_gen_miss
axiom_free amdvi_proofs     test_vector_amdvi_translate_fill_gen_after_invalidate
# P_IOTLB (VT-d 5.20 §6.5.2.4) in the command queue: the PASID-selective
# descriptor plus Invalidation-Wait, and the §6.5.2.2 pairing through the queue
# (PASID-cache eviction half + IOTLB half both cleared).
axiom_free iommu_proofs      iommu_process_queue_piotlb_spec
axiom_free iommu_proofs      iommu_queue_piotlb_pair_clears
axiom_free iommu_proofs      iommu_shootdown_mem
axiom_free iommu_proofs      iommu_shootdown_via_queue_refines_iommu_shootdown
axiom_free tlb_tags         flush_tlb_entry_leaf
axiom_free tlb_tags         flush_tlb_entry_vivt_leaf
axiom_free tlb_tags         filter_tlb_leaf
axiom_free tlb_tags         test_vector_pipt_vivt_agree
axiom_free tlb_tags         test_vector_pipt_vivt_differ
axiom_free tlb_tags         find_tlb_napot_leaf
axiom_free tlb_tags         test_vector_tlb_napot_covers_page
axiom_free tlb_tags         test_vector_tlb_napot_flush
# second MMU variant: MIPS software-refill TLB (+ 1 KiB PageGrain). The Sail
# transcription is mips_tlb.v (generated from mips_tlb.sail); the proofs over the
# generated model live in mips_tlb_proofs.v and the QEMU differential oracle in
# mips_qemu_oracle.v.
axiom_free mips_tlb_proofs  compute_mask_level_unfold
axiom_free mips_tlb_proofs  compute_mask_level_some_even
axiom_free mips_tlb_proofs  mips_refill_lookup_covers
# MIPS shootdown integration (the software-refill twin of coherence/shootdown).
axiom_free mips_tlb_proofs  mips_flush_clears
axiom_free mips_tlb_proofs  mips_unmap_without_flush_breaks_coherence
axiom_free mips_tlb_proofs  mips_refill_flush_composes
axiom_free mips_tlb_proofs  mips_shootdown_correct
axiom_free mips_tlb_proofs  test_vector_mask_lvl0
axiom_free mips_tlb_proofs  test_vector_mask_lvl2
axiom_free mips_tlb_proofs  test_vector_mask_lvl4
axiom_free mips_tlb_proofs  test_vector_mask_odd
axiom_free mips_tlb_proofs  test_vector_mask_nonrun
axiom_free mips_tlb_proofs  test_vector_mask_esp_lvl2
axiom_free mips_tlb_proofs  test_vector_base_shift_1k
axiom_free mips_tlb_proofs  test_vector_base_shift_4k
axiom_free mips_tlb_proofs  test_vector_page_shift_1k
axiom_free mips_tlb_proofs  test_vector_page_shift_4k
axiom_free mips_tlb_proofs  test_vector_page_shift_16k
axiom_free mips_tlb_proofs  test_vector_vpn2x_0
axiom_free mips_tlb_proofs  test_vector_vpn2x_1
axiom_free mips_tlb_proofs  test_vector_vpn2x_2
axiom_free mips_tlb_proofs  test_vector_vpn2x_3
axiom_free mips_tlb_proofs  test_vector_mips_1k_covers
axiom_free mips_tlb_proofs  test_vector_mips_1k_same_page
axiom_free mips_tlb_proofs  test_vector_mips_1k_next_page
axiom_free mips_tlb_proofs  test_vector_mips_4k_covers
axiom_free mips_tlb_proofs  test_vector_mips_4k_same_page
axiom_free mips_tlb_proofs  test_vector_mips_4k_next_page
axiom_free mips_tlb_proofs  test_vector_mips_16k_covers
axiom_free mips_tlb_proofs  test_vector_mips_4k_not_super
axiom_free mips_tlb_proofs  test_vector_mips_pa_1k
axiom_free mips_tlb_proofs  test_vector_mips_pa_4k
axiom_free mips_tlb_proofs  test_vector_mips_pa_16k
axiom_free mips_tlb_proofs  test_vector_mips_refill
axiom_free mips_tlb_proofs  test_vector_mips_flush
axiom_free mips_tlb_proofs  test_vector_mips_flush_preserves_other
# QEMU differential oracle: compute_mask_level transcribes compute_pagemask.
axiom_free mips_qemu_oracle compute_mask_level_conforms
axiom_free mips_qemu_oracle qemu_cto_cto18
axiom_free mips_qemu_oracle diff_decode_lvl0
axiom_free mips_qemu_oracle diff_decode_lvl2
axiom_free mips_qemu_oracle diff_decode_lvl4
axiom_free mips_qemu_oracle diff_decode_odd
axiom_free mips_qemu_oracle diff_decode_nonrun
axiom_free mips_qemu_oracle diff_decode_esp_l2
axiom_free mips_qemu_oracle diff_pa_1k
axiom_free mips_qemu_oracle diff_pa_4k
axiom_free mips_qemu_oracle diff_pa_16k
axiom_free mips_qemu_oracle diff_pa_esp_4k
axiom_free mips_qemu_oracle diff_match_1k_even
axiom_free mips_qemu_oracle diff_match_1k_same
axiom_free mips_qemu_oracle diff_match_1k_pairing
axiom_free mips_qemu_oracle diff_match_4k_next
axiom_free mips_qemu_oracle diff_match_16k_super
# third MMU variant: LoongArch software-refill TLB (odd/even pair, ps spectrum).
axiom_free loongarch_tlb_proofs la_refill_lookup_covers
axiom_free loongarch_tlb_proofs la_flush_clears
axiom_free loongarch_tlb_proofs la_unmap_without_flush_breaks_coherence
axiom_free loongarch_tlb_proofs la_refill_flush_composes
axiom_free loongarch_tlb_proofs la_shootdown_correct
axiom_free loongarch_tlb_proofs test_vector_la_vppn_of
axiom_free loongarch_tlb_proofs test_vector_la_4k_even_covers
axiom_free loongarch_tlb_proofs test_vector_la_4k_odd_covers
axiom_free loongarch_tlb_proofs test_vector_la_4k_next_pair
axiom_free loongarch_tlb_proofs test_vector_la_16k_even_covers
axiom_free loongarch_tlb_proofs test_vector_la_16k_odd_covers
axiom_free loongarch_tlb_proofs test_vector_la_16k_next_pair
axiom_free loongarch_tlb_proofs test_vector_la_4k_not_super
axiom_free loongarch_tlb_proofs test_vector_la_pa_4k_even
axiom_free loongarch_tlb_proofs test_vector_la_pa_4k_odd
axiom_free loongarch_tlb_proofs test_vector_la_pa_16k_even
axiom_free loongarch_tlb_proofs test_vector_la_pa_16k_odd
axiom_free loongarch_tlb_proofs test_vector_la_refill
axiom_free loongarch_tlb_proofs test_vector_la_flush
axiom_free loongarch_tlb_proofs test_vector_la_flush_preserves_other
# LoongArch QEMU differential oracle (match/PA transcription + diff vectors).
axiom_free loongarch_qemu_oracle diff_la_match_4k_even
axiom_free loongarch_qemu_oracle diff_la_match_4k_odd
axiom_free loongarch_qemu_oracle diff_la_match_4k_next
axiom_free loongarch_qemu_oracle diff_la_match_16k_even
axiom_free loongarch_qemu_oracle diff_la_match_16k_odd
axiom_free loongarch_qemu_oracle diff_la_match_16k_next
axiom_free loongarch_qemu_oracle diff_la_pa_4k_even
axiom_free loongarch_qemu_oracle diff_la_pa_4k_odd
axiom_free loongarch_qemu_oracle diff_la_pa_16k_even
axiom_free loongarch_qemu_oracle diff_la_pa_16k_odd
axiom_free loongarch_qemu_oracle diff_la_odd_even
# general conformance: the model/oracle match agrees for every entry/address
# (the shift identity, unblocked by mword_lemmas.v's concrete MachineWord).
axiom_free loongarch_qemu_oracle la_match_shift_conforms
axiom_free loongarch_qemu_oracle la_covers_conforms
axiom_free loongarch_qemu_oracle la_pa_hi_conforms
axiom_free loongarch_qemu_oracle la_pa_conforms
# fourth MMU variant: AArch64 VMSAv8-64 (block descriptors + contpte + LPA2 DS2).
# The Sail transcription is aarch64_tlb.v (from aarch64_tlb.sail); the proofs
# over the generated model live in aarch64_tlb_proofs.v.
axiom_free aarch64_tlb_proofs aa_refill_lookup_covers
axiom_free aarch64_tlb_proofs aa_flush_clears
axiom_free aarch64_tlb_proofs aa_unmap_without_flush_breaks_coherence
axiom_free aarch64_tlb_proofs aa_refill_flush_composes
axiom_free aarch64_tlb_proofs aa_shootdown_correct
axiom_free aarch64_tlb_proofs test_vector_translation_4k_page
axiom_free aarch64_tlb_proofs test_vector_translation_2m_block
axiom_free aarch64_tlb_proofs test_vector_translation_1g_block
axiom_free aarch64_tlb_proofs test_vector_translation_512g_block
axiom_free aarch64_tlb_proofs test_vector_translation_16k_page
axiom_free aarch64_tlb_proofs test_vector_translation_64k_page
axiom_free aarch64_tlb_proofs test_vector_translation_lpa2_4k
axiom_free aarch64_tlb_proofs test_vector_translation_lpa2_1m_block
axiom_free aarch64_tlb_proofs test_vector_contig_4k
axiom_free aarch64_tlb_proofs test_vector_contig_16k_l2
axiom_free aarch64_tlb_proofs test_vector_contig_16k_l3
axiom_free aarch64_tlb_proofs test_vector_contig_64k
axiom_free aarch64_tlb_proofs test_vector_contig_lpa2_4k_l1
axiom_free aarch64_tlb_proofs test_vector_contig_lpa2_4k_l3
axiom_free aarch64_tlb_proofs test_vector_contig_lpa2_64k_l2
axiom_free aarch64_tlb_proofs test_vector_contig_lpa2_64k_l3
axiom_free aarch64_tlb_proofs test_vector_contig_reserved_l0
axiom_free aarch64_tlb_proofs test_vector_aa_4k_covers
axiom_free aarch64_tlb_proofs test_vector_aa_4k_next_page
axiom_free aarch64_tlb_proofs test_vector_aa_2m_covers
axiom_free aarch64_tlb_proofs test_vector_aa_2m_hi_edge
axiom_free aarch64_tlb_proofs test_vector_aa_2m_next_block
axiom_free aarch64_tlb_proofs test_vector_aa_4k_not_super
axiom_free aarch64_tlb_proofs test_vector_aa_contig_covers
axiom_free aarch64_tlb_proofs test_vector_aa_contig_hi_edge
axiom_free aarch64_tlb_proofs test_vector_aa_contig_next
axiom_free aarch64_tlb_proofs test_vector_aa_pa_4k
axiom_free aarch64_tlb_proofs test_vector_aa_pa_2m
axiom_free aarch64_tlb_proofs test_vector_aa_pa_contig
axiom_free aarch64_tlb_proofs test_vector_aa_refill
axiom_free aarch64_tlb_proofs test_vector_aa_flush
axiom_free aarch64_tlb_proofs test_vector_aa_flush_preserves_other
# mword uint-distribution: the SailStdpp mword/shiftr/shiftl/or_vec/zero_extend
# ops unfold to stdpp bv_* and satisfy the word_to_N distribution identities the
# general StageOA proof needs (no axiom; the concrete MachineWord is transparent).
axiom_free mword_lemmas uint_bv_unsigned
axiom_free mword_lemmas uint_nonneg
axiom_free mword_lemmas bv_wrap_mword
axiom_free mword_lemmas bv_modulus_mword
axiom_free mword_lemmas uint_autocast
axiom_free mword_lemmas uint_to_word_idx
axiom_free mword_lemmas bv_unsigned_N_to_word_mword
axiom_free mword_lemmas uint_shiftr
axiom_free mword_lemmas uint_shiftl
axiom_free mword_lemmas uint_or_vec
axiom_free mword_lemmas uint_zero_extend
axiom_free mword_lemmas shift_mod_div
axiom_free mword_lemmas Z_land_mul_pow2_0
axiom_free mword_lemmas Z_lor_add_pow2
axiom_free mword_lemmas uint_subrange_vec_dec_55_0
axiom_free mword_lemmas uint_and_vec
axiom_free mword_lemmas uint_not_vec
axiom_free mword_lemmas uint_mword_of_int
axiom_free mword_lemmas uint_swmask
axiom_free mword_lemmas Z_land_clear_low
# sail-arm differential oracle: the size machinery agrees (general theorems) and
# the StageOA address concat is pinned against aa_pa (vm_compute vectors).
axiom_free aarch64_sail_oracle sa_tgx_granule_bits_conforms
axiom_free aarch64_sail_oracle sa_translation_size_conforms
axiom_free aarch64_sail_oracle sa_contiguous_size_conforms
axiom_free aarch64_sail_oracle sa_ia_msb_conforms
axiom_free aarch64_sail_oracle diff_stage_oa_2m
axiom_free aarch64_sail_oracle diff_stage_oa_4k
axiom_free aarch64_sail_oracle diff_stage_oa_contig
axiom_free aarch64_sail_oracle diff_stage_oa_2m_next
# general (not vm_compute) StageOA identity: aa_pa e va = concat(subrange baseaddr
# 55 ia_msb)(subrange va (ia_msb-1) 0), proved via the mword_lemmas above.
axiom_free aarch64_sail_oracle aa_stage_oa_spec
# pgcl failure-mode vectors: #9 (contpte fold), #10 (TLBI stride), #12 (TSB over-insertion).
axiom_free aarch64_pgcl test_vector_pgcl9_prefold_page0
axiom_free aarch64_pgcl test_vector_pgcl9_prefold_page1
axiom_free aarch64_pgcl test_vector_pgcl9_contig_fold_loses_offset
axiom_free aarch64_pgcl test_vector_pgcl9_contig_fold_mismatch
axiom_free aarch64_pgcl test_vector_pgcl10_page_stride_leaves_stale
axiom_free aarch64_pgcl test_vector_pgcl10_full_flush_clears
axiom_free aarch64_pgcl test_vector_pgcl12_single_demap
axiom_free aarch64_pgcl test_vector_pgcl12_overinsert_stale
axiom_free aarch64_pgcl test_vector_pgcl12_overinsert_count
# pgcl failure-mode vectors #7 (THP split phantom _mapcount) and #8
# (__split_huge_zero_page_pmd loop bound / RSS leak): the sequential M1-M3
# split/mapcount model in pgcl_split.v (plain lists, no Sail types).
axiom_free pgcl_split split_correct_sound
axiom_free pgcl_split huge_zero_split_correct_no_none
axiom_free pgcl_split huge_zero_split_buggy_none_count
axiom_free pgcl_split test_vector_pgcl7_buggy_head_phantom
axiom_free pgcl_split test_vector_pgcl7_buggy_head_no_pte
axiom_free pgcl_split test_vector_pgcl7_buggy_unsound
axiom_free pgcl_split test_vector_pgcl7_correct_head_unmapped
axiom_free pgcl_split test_vector_pgcl7_correct_sound
axiom_free pgcl_split test_vector_pgcl7_buggy_head_phantom_c16
axiom_free pgcl_split test_vector_pgcl8_correct_no_none
axiom_free pgcl_split test_vector_pgcl8_buggy_480_none
axiom_free pgcl_split test_vector_pgcl8_buggy_rss_leak
axiom_free pgcl_split test_vector_pgcl8_correct_rss_leak
axiom_free pgcl_split test_vector_pgcl8_buggy_small_none
axiom_free_drain "$FLAGS"

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
  # S4.2b-2 (first direction): the IOMMU broadcast's leader -> IOMMU doorbell
  # release/acquire, a faithful re-instantiation of shootdown_weak_gen_inv with
  # the request flag as the message.
  # S2.2c: the N-core weak-memory broadcast shootdown over the concrete machine.
  rocq compile $WFLAGS shootdown_weak_broadcast.v
  rocq compile $WFLAGS iommu_broadcast_weak.v
  # S4.5 PASID gpfsl lift: the weak-memory program over the in-loop PASID
  # translation — the leader steps the PASID-cache ghost from the evicted to
  # the refilled cache at the final read (reusing the S4.2b-2 composition),
  # alone or alongside the machine ghost.
  rocq compile $WFLAGS pasid_translate_weak.v
  axiom_free pasid_translate_weak pasid_translate_pc_lift "$WFLAGS"
  axiom_free pasid_translate_weak pasid_translate_pc_machine "$WFLAGS"
  axiom_free pasid_translate_weak pc_ctx_update "$WFLAGS"
  # S4.5 VT-d PASID generation-tag weak lift: the PASID-cache ghost steps
  # from stale-tag eviction to the gen-g fill-on-miss post-state, alone or
  # alongside the machine ghost.
  axiom_free pasid_translate_weak pasid_translate_gen_pc_lift "$WFLAGS"
  axiom_free pasid_translate_weak pasid_translate_gen_pc_machine "$WFLAGS"
  # S4.5 device-side lift: the same weak-memory program over the
  # device-table fill-on-miss loop, with the cache ghost keyed by the DTE's DID.
  rocq compile $WFLAGS vtd_device_translate_weak.v
  axiom_free vtd_device_translate_weak vtd_device_translate_dc_lift "$WFLAGS"
  axiom_free vtd_device_translate_weak vtd_device_translate_dc_machine "$WFLAGS"
  axiom_free vtd_device_translate_weak dc_ctx_update "$WFLAGS"
  # S4.5 weak-memory PRI fault-delivery lift: the FRCD ghost steps from the
  # empty fault queue to the queue with the delivered record at the leader's
  # final read (alone, or alongside the machine ghost); the resolved path is
  # the identity lift (no record delivered).
  rocq compile $WFLAGS pri_fault_weak.v
  axiom_free pri_fault_weak pri_fault_fr_lift "$WFLAGS"
  axiom_free pri_fault_weak pri_fault_fr_silent_lift "$WFLAGS"
  axiom_free pri_fault_weak pri_fault_fr_machine "$WFLAGS"
  axiom_free pri_fault_weak fr_ctx_update "$WFLAGS"
  # S4.5 SMMU/AMD-Vi walker weak lifts: the gpfsl programs over the two
  # second-platform fill-on-miss loops — the SMMU's STE -> CD -> two-stage and
  # AMD-Vi's 4-level walk — with the IOTLB ghost (`sg_ctx` / `ag_ctx`) stepped
  # from the *invalidated* cache to the *refilled* one at the leader's final
  # read, alone or alongside the machine ghost.
  rocq compile $WFLAGS smmu_translate_weak.v
  axiom_free smmu_translate_weak smmu_translate_sg_lift "$WFLAGS"
  axiom_free smmu_translate_weak smmu_translate_sg_machine "$WFLAGS"
  axiom_free smmu_translate_weak sg_ctx_update "$WFLAGS"
  rocq compile $WFLAGS amdvi_translate_weak.v
  axiom_free amdvi_translate_weak amdvi_translate_ag_lift "$WFLAGS"
  axiom_free amdvi_translate_weak amdvi_translate_ag_machine "$WFLAGS"
  axiom_free amdvi_translate_weak ag_ctx_update "$WFLAGS"
  # S4.5 gen-tag weak lifts: the generation-tagged fill-on-miss loops as weak
  # programs — the IOTLB ghost steps from the *evicted* cache (the stale
  # generations cleared by iotlb_evict_gen after a CD / PASID-table re-root)
  # to the *gen-refilled* one, alone or alongside the machine ghost.
  axiom_free smmu_translate_weak smmu_translate_gen_sg_lift "$WFLAGS"
  axiom_free smmu_translate_weak smmu_translate_gen_sg_machine "$WFLAGS"
  axiom_free amdvi_translate_weak amdvi_translate_gen_ag_lift "$WFLAGS"
  axiom_free amdvi_translate_weak amdvi_translate_gen_ag_machine "$WFLAGS"
  # S4.3 ATS device-TLB weak lift: the gpfsl program over the device-TLB
  # invalidation (PCIe ATS §4.3 / the SMMU/AMD-Vi device-side tier) — the
  # devtlb ghost (`dt_ctx`, a ghost_var over the device-TLBs) stepped from the
  # pre-invalidation state to the invalidated one at the leader's final read,
  # alone or alongside the machine ghost.
  rocq compile $WFLAGS ats_devtlb_weak.v
  axiom_free ats_devtlb_weak ats_devtlb_dt_lift "$WFLAGS"
  axiom_free ats_devtlb_weak ats_devtlb_dt_machine "$WFLAGS"
  axiom_free ats_devtlb_weak dt_ctx_update "$WFLAGS"
  # S4.3 ATS *translation* path lift: the device-side fill-on-miss as a weak
  # program — the devtlb ghost steps from the pre-translation cache to the
  # post-translation (refilled-on-hit) one (ats_translate_dt_lift /
  # ats_translate_dt_machine); the walk-fault path is the identity lift (no
  # device-TLB fill — the device issues a PRI page request instead).
  axiom_free ats_devtlb_weak ats_translate_refills_devtlb "$WFLAGS"
  axiom_free ats_devtlb_weak ats_translate_fault_devtlb "$WFLAGS"
  axiom_free ats_devtlb_weak ats_translate_dt_lift "$WFLAGS"
  axiom_free ats_devtlb_weak ats_translate_dt_machine "$WFLAGS"
  axiom_free ats_devtlb_weak ats_translate_fault_dt_lift "$WFLAGS"
  # S4.3 full ATS shootdown lift: the end-to-end teardown as one weak program —
  # the machine ghost steps from the pre-shootdown machine to
  # iommu_shootdown_ats (the S4.2a broadcast cores/IOTLB flush composed with
  # the ATS device-TLB invalidation in a single step), alone or alongside the
  # devtlb ghost to the ATS-invalidated device-TLBs; the refines lemma ties
  # the full teardown to the queue formulation.
  axiom_free ats_devtlb_weak ats_shootdown_full_machine "$WFLAGS"
  axiom_free ats_devtlb_weak ats_shootdown_full_refines "$WFLAGS"
  axiom_free ats_devtlb_weak ats_shootdown_full_machine_dt "$WFLAGS"
  axiom_free iommu_broadcast_weak iommu_broadcast_gen_inv "$WFLAGS"
  axiom_free iommu_broadcast_weak iommu_broadcast_ack_gen_inv "$WFLAGS"
  axiom_free iommu_broadcast_weak iommu_broadcast_full_gen_inv "$WFLAGS"
  axiom_free iommu_broadcast_weak iommu_broadcast_full_gen_inv_machine "$WFLAGS"
  rocq compile $WFLAGS intc_weak_broadcast.v
  # S2.5 (program, full controller in the loop): the device-in-the-loop program
  # (pending/masked/delivery/ipi as per-hart arrays) and its specs.
  rocq compile $WFLAGS shootdown_weak_broadcast_intc.v
  axiom_free shootdown_weak_broadcast_intc bc_init_intc_arrays_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast_intc bc_send_all_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast_intc bc_remote_intc_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast_intc bc_fork_remotes_intc_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast_intc bc_wait_all_intc_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast_intc bc_broadcast_intc_spec "$WFLAGS"
  # the interrupt-context delivery gate at the program level: the ack holds the
  # IPI when delivery[i] is suppressed (no doorbell — no loss) and rings the
  # doorbell when delivery is enabled; the context-toggle ops move between them.
  axiom_free shootdown_weak_broadcast_intc intc_enter_context_op_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast_intc intc_exit_context_op_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast_intc intc_ack_op_hold_spec "$WFLAGS"
  axiom_free shootdown_weak_broadcast_intc intc_ack_op_deliver_spec "$WFLAGS"
  # S4.5 PRQ -> INTC weak lift: the fault-message delivery through the
  # interrupt-controller delivery gate (masked/delivery in the loop — the ack
  # rings when enabled, holds when in context) and the FRCDR drain composed
  # into the weak PRI delivery post-state (the ghost post-state is the drained
  # queue and the recovered controller).
  rocq compile $WFLAGS pri_fault_intc_weak.v
  axiom_free pri_fault_intc_weak pri_fault_intc_delivers "$WFLAGS"
  axiom_free pri_fault_intc_weak pri_fault_intc_gated "$WFLAGS"
  axiom_free pri_fault_intc_weak pri_fault_intc_drain_lift "$WFLAGS"
  axiom_free pri_fault_intc_weak pri_fault_intc_drain_machine "$WFLAGS"
  axiom_free pri_fault_intc_weak pri_fault_ack_line_raised "$WFLAGS"
  axiom_free pri_fault_intc_weak pri_fault_ack_unmasked_rings "$WFLAGS"
  axiom_free pri_fault_intc_weak pri_fault_ack_in_context_holds "$WFLAGS"
  axiom_free pri_fault_intc_weak pri_fault_deliver_drain_cycle "$WFLAGS"
  axiom_free pri_fault_intc_weak fr_intc_update "$WFLAGS"
  axiom_free pri_fault_intc_weak fr_intc_machine_update "$WFLAGS"
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
  # S2.5: the S2.4 weak-memory ghost step is the interrupt controller's
  # send+ack (SSG-3) — the device realizes the broadcast's IPI delivery.
  axiom_free intc_weak_broadcast bc_machine_ipi_step_via_intc "$WFLAGS"
  axiom_free intc_weak_broadcast bc_machine_ipi_step_via_intc_cores "$WFLAGS"
  axiom_free_drain "$WFLAGS"
else
  echo "(skip S2.2: gpfsl not found at $GP — check out the third_party/gpfsl submodule)" >&2
fi

echo "OK: hardware model generated and checked (axiom-free)."

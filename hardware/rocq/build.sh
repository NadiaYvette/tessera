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

# --- 3. generate Rocq (SailStdpp style) ---
sail "$SRC" --rocq --rocq-output-dir "$HERE" -o machine
sail "$MIPS_SRC" --rocq --rocq-output-dir "$HERE" -o mips_tlb
sail "$LA_SRC" --rocq --rocq-output-dir "$HERE" -o loongarch_tlb
sail "$AA_SRC" --rocq --rocq-output-dir "$HERE" -o aarch64_tlb
sail "$SA_SRC" --rocq --rocq-output-dir "$HERE" -o sail_arm_tlb
sail "$INTC_SRC" --rocq --rocq-output-dir "$HERE" -o intc

# Dev stdpp (9c7afbb6) lowered its singleton notations {[ x ]} / {[ k := a ]}
# to level 0, while Sail emits record-update notations
# {[ r 'with' field := e ]} at level 1; the two then have an incompatible
# prefix and {[ k := a ]} stops parsing.  Move the (unused) record-update
# notations to level 0 to restore coexistence with stdpp's singletons.
sed -i 's/\(Build_.*\)(at level 1)\./\1(at level 0)./' "$HERE/machine_types.v" "$HERE/mips_tlb_types.v" "$HERE/loongarch_tlb_types.v" "$HERE/aarch64_tlb_types.v" "$HERE/sail_arm_tlb_types.v" "$HERE/intc_types.v"

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
rocq compile $FLAGS mword_lemmas.v
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
rocq compile $FLAGS conformance.v
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
axiom_free conformance      oracle_non_leaf_is_negb_is_leaf
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
  # S2.2c: the N-core weak-memory broadcast shootdown over the concrete machine.
  rocq compile $WFLAGS shootdown_weak_broadcast.v
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

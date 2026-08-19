(* Tessera — the end-to-end proving pass, Stage 2, S2.0 (pure / sequential).

   The N-core broadcast shootdown, *sequentially*, over the generated Sv39 machine:
   core 0 removes the leaf PTE for `va` and invalidates every core's TLB
   (sfence_vma_va), and we prove that afterwards *no* core translates `va` (the
   freed frame) — `translate = None ∧ tlb_lookup = None` on every core.

   This is the pure target property the concurrent Iris proof (S2.1) must
   re-establish under a message-passing schedule. It reuses Stage 1.1's
   leaf-removal lemmas (coherence_leaf.v) and Stage 1's sfence lemmas
   (coherence.v); the only new ingredient is the Forall over the core list.

   See ../../doc/stage2-shootdown.md. *)

Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import coherence.       (* translate_sfence_invariant, sfence_vma_va_clears *)
Require Import coherence_leaf.  (* unmap_leaf_mem, leaf_addr_removal_faults,
                                   leaf_addr_none_implies_translate_none, remove_entry *)
Import ListNotations.

(* A core with a given page-table root and an empty TLB. *)
Definition core_with_root (root : mword 44) : Core :=
  {| Core_satp_ppn := root; Core_tlb := []; Core_hart := 0; Core_node := 0 |}.

(* The broadcast shootdown: remove the leaf PTE for `va` (using page-table root
   `root`) and invalidate every core's TLB. *)
Definition shootdown (m : Machine) (root : mword 44) (va : mword 64) : Machine :=
  {| Machine_mem := unmap_leaf_mem (core_with_root root) m.(Machine_mem) va;
     Machine_cores := List.map (fun c => sfence_vma_va c va) m.(Machine_cores);
     Machine_ram := m.(Machine_ram);
     Machine_ipi := m.(Machine_ipi);
     Machine_iotlb := m.(Machine_iotlb); Machine_devtlbs := m.(Machine_devtlbs); Machine_prireqs := m.(Machine_prireqs) |}.

(* ============================================================
   Lemmas.
   ============================================================ *)

(* `translate` depends on the core only through its satp_ppn. *)
Lemma translate_satp_congr (c1 c2 : Core) (mem : list MemEntry) (va : mword 64) :
  c1.(Core_satp_ppn) = c2.(Core_satp_ppn) ->
  translate c1 mem va = translate c2 mem va.
Proof.
  intros H. unfold translate. rewrite H. reflexivity.
Qed.

(* After the PTE write alone (leaf removal), the walk faults. *)
Lemma translate_faults_after_shootdown_mem (root : mword 44) (mem : list MemEntry) (va : mword 64) :
  translate (core_with_root root) (unmap_leaf_mem (core_with_root root) mem va) va = None.
Proof.
  unfold unmap_leaf_mem.
  destruct (leaf_addr (core_with_root root) mem va) as [a |] eqn:Hl.
  - apply (leaf_addr_removal_faults (core_with_root root) mem va a Hl).
  - apply (leaf_addr_none_implies_translate_none (core_with_root root) mem va Hl).
Qed.

(* Per-core: after its TLB is invalidated (sfence) and the PTE removed, this core
   neither translates `va` nor answers from its TLB. *)
Lemma shootdown_core (root : mword 44) (mem : list MemEntry) (va : mword 64) (c : Core) :
  c.(Core_satp_ppn) = root ->
  translate (sfence_vma_va c va) (unmap_leaf_mem (core_with_root root) mem va) va = None /\
  tlb_lookup (sfence_vma_va c va) va = None.
Proof.
  intros Hsatp. split.
  - rewrite translate_sfence_invariant.
    rewrite (translate_satp_congr c (core_with_root root) (unmap_leaf_mem (core_with_root root) mem va) va Hsatp).
    apply translate_faults_after_shootdown_mem.
  - apply sfence_vma_va_clears.
Qed.

(* ============================================================
   The shootdown theorem.
   ============================================================ *)

(* After the broadcast shootdown, no core translates the freed frame.
   (Vacuous when `Machine_cores` is empty; no `cores <> []` precondition needed.) *)
Theorem shootdown_correct (m : Machine) (root : mword 44) (va : mword 64) :
  Forall (fun c => c.(Core_satp_ppn) = root) m.(Machine_cores) ->
  Forall (fun c => translate c (shootdown m root va).(Machine_mem) va = None /\
                   tlb_lookup c va = None)
         (shootdown m root va).(Machine_cores).
Proof.
  destruct m as [cores mem]. cbn.
  intros Hroot.
  unfold shootdown; cbn.
  rewrite Forall_map.
  induction cores as [| c cs IH].
  - constructor.
  - constructor.
    + apply (shootdown_core root mem va c). apply (Forall_inv Hroot).
    + apply IH. apply (Forall_inv_tail Hroot).
Qed.

(* ============================================================
   The S2.1 reification bridge: the broadcast's reified post-state.
   ============================================================ *)

(* An empty TLB is unchanged by SFENCE.VMA — nothing cached to drop. *)
Lemma sfence_vma_va_empty (c : Core) (va : mword 64) :
  c.(Core_tlb) = [] -> sfence_vma_va c va = c.
Proof.
  destruct c as [satp tlb hart node]. cbn. intros ->. cbn. reflexivity.
Qed.

(* SFENCE-ing a list of empty-TLB cores is the identity (list form of the above). *)
Lemma map_sfence_empty (root : mword 44) (va : mword 64) (n : nat) :
  List.map (fun c => sfence_vma_va c va) (List.map (fun _ => core_with_root root) (seq 0 n)) =
  List.map (fun _ => core_with_root root) (seq 0 n).
Proof.
  rewrite List.map_map.
  apply List.map_ext_in. intros a _. apply sfence_vma_va_empty. reflexivity.
Qed.

(* The broadcast's reified post-state (S2.1): n cores sharing the page-table root
   with empty TLBs, and the leaf PTE for `va` removed. This is `shootdown` applied
   to the machine whose cores are all `core_with_root root`; citing
   `shootdown_correct` yields the S2.0 conclusion on every core. *)
Lemma shootdown_empty_cores (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) :
  Forall (fun c => translate c (unmap_leaf_mem (core_with_root root) mem va) va = None /\
                   tlb_lookup c va = None)
         (List.map (fun _ => core_with_root root) (seq 0 n)).
Proof.
  assert (Hroot : Forall (fun c => c.(Core_satp_ppn) = root)
                        (List.map (fun _ => core_with_root root) (seq 0 n))).
  { rewrite Forall_map. apply Forall_forall. intros x _. reflexivity. }
  specialize (shootdown_correct
    {| Machine_mem := mem;
       Machine_cores := List.map (fun _ => core_with_root root) (seq 0 n);
       Machine_ram := [];
       Machine_ipi := [];
       Machine_iotlb := []; Machine_devtlbs := []; Machine_prireqs := [] |}
    root va Hroot) as H.
  cbn in H. rewrite map_sfence_empty in H. exact H.
Qed.

(* ============================================================
   The break-before-make variant: invalidate the leaf PTE (write an invalid PTE)
   rather than remove it — the faithful model of the broadcast program.
   ============================================================ *)

(* Per-core: after the leaf PTE is written invalid and this core's TLB is
   invalidated, the core neither translates `va` nor answers from its TLB. *)
Lemma invalidate_shootdown_core (root : mword 44) (mem : list MemEntry) (va : mword 64) (p : Pte) (c : Core) :
  p.(Pte_valid) = false ->
  c.(Core_satp_ppn) = root ->
  translate (sfence_vma_va c va) (invalidate_leaf_mem (core_with_root root) mem va p) va = None /\
  tlb_lookup (sfence_vma_va c va) va = None.
Proof.
  intros Hinv Hsatp. split.
  - rewrite translate_sfence_invariant.
    rewrite (translate_satp_congr c (core_with_root root) (invalidate_leaf_mem (core_with_root root) mem va p) va Hsatp).
    unfold invalidate_leaf_mem.
    destruct (leaf_addr (core_with_root root) mem va) as [a |] eqn:Hl.
    + apply (invalidate_leaf_faults (core_with_root root) mem va a p Hl Hinv).
    + apply (leaf_addr_none_implies_translate_none (core_with_root root) mem va Hl).
  - apply sfence_vma_va_clears.
Qed.

(* The invalidate-shootdown: write the leaf PTE for `va` to invalid `p` and
   invalidate every core's TLB (break-before-make), vs `shootdown`'s removal. *)
Definition invalidate_shootdown (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) : Machine :=
  {| Machine_mem := invalidate_leaf_mem (core_with_root root) m.(Machine_mem) va p;
     Machine_cores := List.map (fun c => sfence_vma_va c va) m.(Machine_cores);
     Machine_ram := m.(Machine_ram);
     Machine_ipi := m.(Machine_ipi);
     Machine_iotlb := m.(Machine_iotlb); Machine_devtlbs := m.(Machine_devtlbs); Machine_prireqs := m.(Machine_prireqs) |}.

Theorem invalidate_shootdown_correct (m : Machine) (root : mword 44) (va : mword 64) (p : Pte) :
  p.(Pte_valid) = false ->
  Forall (fun c => c.(Core_satp_ppn) = root) m.(Machine_cores) ->
  Forall (fun c => translate c (invalidate_shootdown m root va p).(Machine_mem) va = None /\
                   tlb_lookup c va = None)
         (invalidate_shootdown m root va p).(Machine_cores).
Proof.
  destruct m as [cores mem]. cbn.
  intros Hinv Hroot.
  unfold invalidate_shootdown; cbn.
  rewrite Forall_map.
  induction cores as [| c cs IH].
  - constructor.
  - constructor.
    + apply (invalidate_shootdown_core root mem va p c Hinv). apply (Forall_inv Hroot).
    + apply IH. apply (Forall_inv_tail Hroot).
Qed.

(* The invalidate variant of the reification bridge: n empty-TLB cores sharing
   the root, with the leaf PTE written invalid — cites `invalidate_shootdown_correct`. *)
Lemma invalidate_shootdown_empty_cores (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) (p : Pte) :
  p.(Pte_valid) = false ->
  Forall (fun c => translate c (invalidate_leaf_mem (core_with_root root) mem va p) va = None /\
                   tlb_lookup c va = None)
         (List.map (fun _ => core_with_root root) (seq 0 n)).
Proof.
  intros Hinv.
  assert (Hroot : Forall (fun c => c.(Core_satp_ppn) = root)
                        (List.map (fun _ => core_with_root root) (seq 0 n))).
  { rewrite Forall_map. apply Forall_forall. intros x _. reflexivity. }
  specialize (invalidate_shootdown_correct
    {| Machine_mem := mem;
       Machine_cores := List.map (fun _ => core_with_root root) (seq 0 n);
       Machine_ram := [];
       Machine_ipi := [];
       Machine_iotlb := []; Machine_devtlbs := []; Machine_prireqs := [] |}
    root va p Hinv Hroot) as H.
  cbn in H. rewrite map_sfence_empty in H. exact H.
Qed.

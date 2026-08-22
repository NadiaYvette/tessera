(* Tessera — G1 upstream-bridge: the shared `walk_decision` agrees with the
   *verbatim upstream* `sail-riscv` PTE predicates.

   The trust-line plan (doc/trust-line-plan.md, Steps 3+4; rigor-trust-line.md
   §5 G1, the "upstream-bridge half") asks that the shared walk decision —
   `walk_decision` in `machine.sail` — be mechanically linked to the *actual
   upstream* `sail-riscv` `pt_walk`, not just to Tessera's own `machine.sail`.

   The full upstream model is a ~80-file closure (prelude → core → exceptions →
   pmp → sys) with externs (`menvcfg`, `currentlyEnabled`, ...); generating it
   whole to Rocq is the documented "larger effort".  The leaf that matters for
   the walk decision is the upstream PTE predicates — `pte_is_non_leaf`
   (vmem_pte.sail ll. 69-71) and `pte_is_invalid` (ll. 89-109) — lifted from
   the `bits(64)`/`PTE_Flags`/`PTE_Ext` bitfields to the flag booleans
   `walk_decision` already takes.  `machine.sail` now carries those predicates
   verbatim (`upstream_pte_is_non_leaf`, `upstream_pte_is_invalid`, in the Sv39
   fragment with Svnapot enabled, SSE=0, reserved-bits-must-be-zero, A/D/U
   assumed zero).  This file proves the bridge:

     walk_decision v r w x n lvl = WalkFault  iff  invalid v r w x n
                                                  or (not invalid /\ not non_leaf /\ lvl > 0)
     walk_decision v r w x n lvl = WalkPointer iff  not invalid /\ non_leaf r w x
     walk_decision v r w x n lvl = WalkLeaf    iff  not invalid /\ not non_leaf /\ not n /\ lvl <= 0
     walk_decision v r w x n lvl = WalkNAPOT   iff  not invalid /\ not non_leaf /\ n /\ lvl <= 0

   The superpage disjunct (leaf at level>0 faults in `walk_decision`) is the
   documented fragment boundary: the Tessera fragment does not model superpages,
   so it faults where upstream would compose a superpage.  Everything else —
   the invalid / non-leaf / leaf / NAPOT decisions — is now *the same artifact*
   in both models (generated from one `machine.sail`), with the upstream
   predicates transcribed verbatim and machine-checked against it here.

   All theorems are closed under the global context (axiom-free); `build.sh`
   enforces this. *)

Require Import Bool.
Require Import ZArith.
Require Import machine_types.
Require Import machine.

(* The four bridge lemmas.  `upstream_pte_is_invalid` / `upstream_pte_is_non_leaf`
   are the verbatim upstream predicates (from machine.v, generated from
   machine.sail); `walk_decision` is the shared decision both `translate` and
   the conformance oracle call. *)

(* 1. WalkFault: either the upstream invalid predicate holds (V=0, R=0&W=1, or
      non-leaf&N=1 reserved), or — the fragment boundary — a valid leaf at
      level>0 (a superpage, not modeled). *)
Theorem walk_decision_fault_iff
  (valid read write exec napot : bool) (lvl : Z) :
  walk_decision valid read write exec napot lvl = WalkFault <->
  (upstream_pte_is_invalid valid read write exec napot = true
   \/ (upstream_pte_is_invalid valid read write exec napot = false
       /\ upstream_pte_is_non_leaf read write exec = false
       /\ Z.gtb lvl 0 = true)).
Proof.
  unfold walk_decision, upstream_pte_is_invalid, upstream_pte_is_non_leaf.
  destruct valid; destruct read; destruct write; destruct exec; destruct napot;
    destruct (Z.gtb lvl 0); simpl; split; intros H; try (discriminate H);
    simpl in *; firstorder congruence.
Qed.

(* 2. WalkPointer: a valid non-leaf pointer (R=W=X=0) with N=0.  The N=1
      non-leaf is upstream-invalid (pte_is_invalid's "non-leaf & ext bits ≠ 0"),
      so `not invalid` excludes it — mirroring `pte_is_invalid`. *)
Theorem walk_decision_pointer_iff
  (valid read write exec napot : bool) (lvl : Z) :
  walk_decision valid read write exec napot lvl = WalkPointer <->
  (upstream_pte_is_invalid valid read write exec napot = false
   /\ upstream_pte_is_non_leaf read write exec = true).
Proof.
  unfold walk_decision, upstream_pte_is_invalid, upstream_pte_is_non_leaf.
  destruct valid; destruct read; destruct write; destruct exec; destruct napot;
    destruct (Z.gtb lvl 0); simpl; split; intros H; try (discriminate H);
    simpl in *; firstorder congruence.
Qed.

(* 3. WalkLeaf: a valid leaf (not non-leaf) at level 0 with N=0. *)
Theorem walk_decision_leaf_iff
  (valid read write exec napot : bool) (lvl : Z) :
  walk_decision valid read write exec napot lvl = WalkLeaf <->
  (upstream_pte_is_invalid valid read write exec napot = false
   /\ upstream_pte_is_non_leaf read write exec = false
   /\ napot = false
   /\ Z.gtb lvl 0 = false).
Proof.
  unfold walk_decision, upstream_pte_is_invalid, upstream_pte_is_non_leaf.
  destruct valid; destruct read; destruct write; destruct exec; destruct napot;
    destruct (Z.gtb lvl 0); simpl; split; intros H; try (discriminate H);
    simpl in *; firstorder congruence.
Qed.

(* 4. WalkNAPOT: a valid NAPOT leaf (N=1) at level 0. *)
Theorem walk_decision_napot_iff
  (valid read write exec napot : bool) (lvl : Z) :
  walk_decision valid read write exec napot lvl = WalkNAPOT <->
  (upstream_pte_is_invalid valid read write exec napot = false
   /\ upstream_pte_is_non_leaf read write exec = false
   /\ napot = true
   /\ Z.gtb lvl 0 = false).
Proof.
  unfold walk_decision, upstream_pte_is_invalid, upstream_pte_is_non_leaf.
  destruct valid; destruct read; destruct write; destruct exec; destruct napot;
    destruct (Z.gtb lvl 0); simpl; split; intros H; try (discriminate H);
    simpl in *; firstorder congruence.
Qed.

(* ============================================================
   Executable test vectors: the bridge on the concrete encodings
   `walk_decision`'s call sites feed it (level 2 / 1 / 0 of the Sv39 walk).
   Discharged by computation.  Each pins one branch of the upstream
   predicates. *)

(* An upstream-invalid PTE (V=0) always faults, at any level. *)
Lemma bridge_vec_invalid_v0 : walk_decision false true false false false 2 = WalkFault.
Proof. vm_compute. reflexivity. Qed.

(* The reserved write-only encoding (R=0, W=1, X=0): upstream-invalid, faults. *)
Lemma bridge_vec_writeonly : walk_decision true false true false false 1 = WalkFault.
Proof. vm_compute. reflexivity. Qed.

(* A non-leaf pointer (R=W=X=0, N=0) at level 1 descends. *)
Lemma bridge_vec_pointer : walk_decision true false false false false 1 = WalkPointer.
Proof. vm_compute. reflexivity. Qed.

(* A non-leaf pointer with N=1 is reserved (pte_is_invalid's non-leaf & ext
   bits ≠ 0): faults, not a pointer. *)
Lemma bridge_vec_pointer_napot : walk_decision true false false false true 2 = WalkFault.
Proof. vm_compute. reflexivity. Qed.

(* A read-only leaf at level 0 translates. *)
Lemma bridge_vec_leaf : walk_decision true true false false false 0 = WalkLeaf.
Proof. vm_compute. reflexivity. Qed.

(* A NAPOT leaf (N=1) at level 0 is a NAPOT page. *)
Lemma bridge_vec_napot : walk_decision true true false false true 0 = WalkNAPOT.
Proof. vm_compute. reflexivity. Qed.

(* The fragment boundary: a valid leaf at level 1 (a 1 GiB superpage) faults in
   this fragment (superpages not modeled), yet the upstream invalid predicate
   does not hold — the fault is the superpage boundary, not PTE invalidity. *)
Lemma bridge_vec_superpage_not_invalid :
  upstream_pte_is_invalid true true false false false = false.
Proof. vm_compute. reflexivity. Qed.

Lemma bridge_vec_superpage_faults : walk_decision true true false false false 1 = WalkFault.
Proof. vm_compute. reflexivity. Qed.

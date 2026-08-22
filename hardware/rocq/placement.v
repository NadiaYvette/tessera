(* Tessera — SSG-1: topology-aware placement theorems.

   Core placement properties that depend on the SSG-9 grouping hierarchy:
   - Co-resident cores (same node) share TLB state
   - NUMA-local allocation never aliases remote frames
   - Cross-node communication uses message passing

   This file is axiom-free (except the generic same_node_implies_same_domain). *)

From Stdlib Require Import Bool ZArith List.
Require Import machine_types.
Require Import machine.
Require Import topology.

(* --- Core placement queries --- *)

Definition same_node (topo : Topology) (c1 c2 : nat) : Prop :=
  exists n, In n topo.(topo_nodes) /\
    In c1 n.(node_cores) /\ In c2 n.(node_cores).

Definition same_domain (topo : Topology) (c1 c2 : nat) : Prop :=
  exists d nid n,
    In d topo.(topo_domains) /\
    In nid d.(dom_nodes) /\
    find_node topo.(topo_nodes) (Z.of_nat nid) = Some n /\
    In c1 n.(node_cores) /\ In c2 n.(node_cores).

(* --- Placement theorems --- *)

(* Generic version requires two bridge lemmas:
   1. node_in_domain d n.(node_id) = true -> In (Z.to_nat n.(node_id)) d.(dom_nodes)
   2. In n topo.(topo_nodes) -> find_node topo.(topo_nodes) n.(node_id) = Some n
   Left Admitted until the bridge lemmas are proven. *)
Theorem same_node_implies_same_domain :
  forall topo c1 c2,
    same_node topo c1 c2 -> same_domain topo c1 c2.
Proof.
  intros topo c1 c2 H. unfold same_domain, same_node in *.
  destruct H as [n [Hn_mem [Hc1 Hc2]]].
  admit.
Admitted.

(* Concrete version: fully proved for example_topo via direct case analysis.
   Key subtlety: example_domain0 is the HEAD of topo_domains but
   example_domain1 is the TAIL, so the second case needs in_cons. *)
Theorem concrete_same_node_implies_same_domain :
  forall c1 c2, same_node example_topo c1 c2 -> same_domain example_topo c1 c2.
Proof.
  intros c1 c2 [n [Hn_mem [Hc1 Hc2]]].
  apply in_inv in Hn_mem.
  destruct Hn_mem as [Heq | Hn_mem].
  - (* n = example_node0: domain0 is the HEAD of topo_domains *)
    subst.
    exists example_domain0, 0%nat, example_node0.
    split; [apply in_eq |].
    split; [| split; [reflexivity | split; [exact Hc1 | exact Hc2]]].
    change (dom_nodes example_domain0) with (0%nat :: nil).
    apply in_eq.
  - apply in_inv in Hn_mem.
    destruct Hn_mem as [Heq | Habs].
    + (* n = example_node1: domain1 is the TAIL — need in_cons *)
      subst.
      exists example_domain1, 1%nat, example_node1.
      split; [apply in_cons; apply in_eq |].
      split; [| split; [reflexivity | split; [exact Hc1 | exact Hc2]]].
      change (dom_nodes example_domain1) with (1%nat :: nil).
      apply in_eq.
    + contradiction.
Qed.

(* --- Concrete test vectors --- *)

Lemma node0_cores : node_cores example_node0 = cons 0%nat (cons 1%nat nil).
Proof. reflexivity. Qed.

Lemma node1_cores : node_cores example_node1 = cons 2%nat (cons 3%nat nil).
Proof. reflexivity. Qed.

Lemma domain0_nodes : dom_nodes example_domain0 = cons 0%nat nil.
Proof. reflexivity. Qed.

Lemma domain1_nodes : dom_nodes example_domain1 = cons 1%nat nil.
Proof. reflexivity. Qed.

Lemma node0_mem : node_mem_start example_node0 = 0 /\
                  node_mem_end example_node0 = 34359738368.
Proof. split; reflexivity. Qed.

Lemma node1_mem : node_mem_start example_node1 = 34359738368 /\
                  node_mem_end example_node1 = 68719476736.
Proof. split; reflexivity. Qed.

Lemma node_mem_adjacent :
  node_mem_end example_node0 = node_mem_start example_node1.
Proof. reflexivity. Qed.

Lemma find_node_0_is_node0 :
  find_node (topo_nodes example_topo) 0 = Some example_node0.
Proof. reflexivity. Qed.

Lemma find_node_1_is_node1 :
  find_node (topo_nodes example_topo) 1 = Some example_node1.
Proof. reflexivity. Qed.

(* --- Concrete placement test vectors --- *)

Lemma core0_core1_same_node :
  same_node example_topo 0%nat 1%nat.
Proof.
  exists example_node0. split.
  - apply in_eq.
  - split.
    + apply in_eq.
    + apply in_cons. apply in_eq.
Qed.

Lemma core0_core1_same_domain :
  same_domain example_topo 0%nat 1%nat.
Proof.
  exact (concrete_same_node_implies_same_domain 0%nat 1%nat core0_core1_same_node).
Qed.

Lemma core2_core3_same_node :
  same_node example_topo 2%nat 3%nat.
Proof.
  exists example_node1. split.
  - apply in_cons. apply in_eq.
  - split.
    + apply in_eq.
    + apply in_cons. apply in_eq.
Qed.

Lemma core2_core3_same_domain :
  same_domain example_topo 2%nat 3%nat.
Proof.
  exact (concrete_same_node_implies_same_domain 2%nat 3%nat core2_core3_same_node).
Qed.

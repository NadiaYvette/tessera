(* Tessera — SSG-1: topology-aware placement theorems.

   Core placement properties that depend on the SSG-9 grouping hierarchy.
   Axiom-free: the generic same_node_implies_same_domain requires topo_wf
   (topology well-formedness) as a hypothesis; the concrete version is proved
   directly for example_topo. *)

From Stdlib Require Import Bool ZArith List Lia.
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

(* --- Bridge lemmas --- *)

Lemma node_in_domain_true_In :
  forall nodes nid,
    node_in_domain nodes nid = true -> In nid nodes.
Proof.
  induction nodes as [|h t IH].
  - intros nid H. discriminate H.
  - intros nid H. simpl in H.
    destruct (Nat.eqb h nid) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. apply in_eq.
    + apply in_cons. apply IH. exact H.
Qed.

Lemma find_node_In :
  forall nodes nid n,
    find_node nodes nid = Some n -> In n nodes.
Proof.
  induction nodes as [|h t IH].
  - intros nid n H. discriminate H.
  - intros nid n H. simpl in H.
    destruct (Z.eqb (node_id h) nid) eqn:Heq.
    + injection H as <-. apply in_eq.
    + apply IH in H. apply in_cons. exact H.
Qed.

Lemma find_node_node_id :
  forall nodes nid n,
    find_node nodes nid = Some n -> node_id n = nid.
Proof.
  induction nodes as [|h t IH].
  - intros nid n H. discriminate H.
  - intros nid n H. simpl in H.
    destruct (Z.eqb (node_id h) nid) eqn:Heq.
    + assert (Hh : h = n) by (injection H as <-; reflexivity).
      subst. apply Z.eqb_eq. exact Heq.
    + apply IH. exact H.
Qed.

Lemma find_node_In_Some :
  forall nodes n,
    In n nodes -> find_node nodes (node_id n) <> None.
Proof.
  induction nodes as [|h t IH].
  - intros n H. contradiction.
  - intros n H. simpl.
    destruct (Z.eqb (node_id h) (node_id n)) eqn:Heq.
    + discriminate.
    + apply IH. destruct H as [-> | H].
      * exfalso. apply Z.eqb_neq in Heq. apply Heq. reflexivity.
      * exact H.
Qed.

(* --- Placement theorems --- *)

Definition topo_wf (topo : Topology) : Prop :=
  (forall n, In n topo.(topo_nodes) ->
    node_id n >= 0 /\
    exists d, In d topo.(topo_domains) /\
      node_in_domain d.(dom_nodes) (Z.to_nat n.(node_id)) = true) /\
  (forall n1 n2, In n1 topo.(topo_nodes) -> In n2 topo.(topo_nodes) ->
    node_id n1 = node_id n2 -> n1 = n2).

Theorem same_node_implies_same_domain :
  forall topo c1 c2,
    topo_wf topo ->
    same_node topo c1 c2 -> same_domain topo c1 c2.
Proof.
  intros topo c1 c2 [Hwf_nid Huniq] [n [Hn_mem [Hc1 Hc2]]].
  unfold same_domain.
  specialize (Hwf_nid n Hn_mem) as [Hn_ge0 [d [Hd_mem Hd_dom]]].
  apply node_in_domain_true_In in Hd_dom as Hnid_mem.
  remember (Z.to_nat n.(node_id)) as nid eqn:Heq_nid.
  exists d, nid.
  (* find_node must succeed because n is in the list *)
  assert (Hfn : exists n', find_node topo.(topo_nodes) (Z.of_nat nid) = Some n').
  { destruct (find_node topo.(topo_nodes) (Z.of_nat nid)) eqn:Hfn_eq.
    - exists n0. reflexivity.
    - exfalso.
      assert (HZN : Z.of_nat nid = node_id n).
      { subst nid. lia. }
      assert (Habs : find_node topo.(topo_nodes) (node_id n) <> None).
      { apply find_node_In_Some. exact Hn_mem. }
      rewrite <- HZN in Habs. apply Habs. exact Hfn_eq. }
  destruct Hfn as [n' Hfn'].
  exists n'.
  split; [exact Hd_mem |].
  split; [exact Hnid_mem |].
  split; [exact Hfn' |].
  (* n' has node_id = Z.of_nat nid = n.(node_id) and is in topo_nodes *)
  assert (Hn'_id : node_id n' = node_id n).
  { assert (HZN : Z.of_nat nid = node_id n).
    { rewrite Heq_nid. lia. }
    rewrite <- HZN. exact (find_node_node_id _ _ _ Hfn'). }
  assert (Hn'_in : In n' topo.(topo_nodes)).
  { apply find_node_In with (nid := Z.of_nat nid). exact Hfn'. }
  assert (Hn'_eq : n' = n).
  { apply Huniq; auto. }
  split; [subst; exact Hc1 | subst; exact Hc2].
Qed.

(* --- Concrete version --- *)

Theorem concrete_same_node_implies_same_domain :
  forall c1 c2, same_node example_topo c1 c2 -> same_domain example_topo c1 c2.
Proof.
  intros c1 c2 [n [Hn_mem [Hc1 Hc2]]].
  apply in_inv in Hn_mem.
  destruct Hn_mem as [Heq | Hn_mem].
  - subst.
    exists example_domain0, 0%nat, example_node0.
    split; [apply in_eq |].
    split; [| split; [reflexivity | split; [exact Hc1 | exact Hc2]]].
    change (dom_nodes example_domain0) with (0%nat :: nil).
    apply in_eq.
  - apply in_inv in Hn_mem.
    destruct Hn_mem as [Heq | Habs].
    + subst.
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

(* Prove example_topo satisfies topo_wf *)
Lemma example_topo_wf : topo_wf example_topo.
Proof.
  split.
  - intros n Hn. cbn in Hn.
    destruct Hn as [<- | [<- | Habs]].
    + split. { simpl. lia. }
      exists example_domain0. split.
      * apply in_eq.
      * change (dom_nodes example_domain0) with (0%nat :: nil). reflexivity.
    + split. { simpl. lia. }
      exists example_domain1. split.
      * apply in_cons. apply in_eq.
      * change (dom_nodes example_domain1) with (1%nat :: nil). reflexivity.
    + contradiction.
  - intros n1 n2 Hn1 Hn2 Hid.
    cbn in Hn1. cbn in Hn2.
    destruct Hn1 as [<- | [<- | Habs1]].
    + destruct Hn2 as [<- | [<- | Habs2]].
      * reflexivity.
      * exfalso. simpl in Hid. lia.
      * contradiction.
    + destruct Hn2 as [<- | [<- | Habs2]].
      * exfalso. simpl in Hid. lia.
      * reflexivity.
      * contradiction.
    + contradiction.
Qed.

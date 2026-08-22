(* Tessera — SSG-9: the grouping hierarchy — Node, Domain, and topology.

   The generated Machine record has a flat `list Core`.  This file layers
   the SSG-9 grouping hierarchy *on top* of the generated model without
   modifying it:

   - [Node]: a NUMA node — a group of Cores sharing node-local memory.
   - [Domain]: a multikernel domain — a group of Nodes (Barrelfish-like).
   - [Topology]: a partition of Machine_cores into Nodes, each in a Domain.

   The key invariant: within a domain, cores share memory (full weak-memory
   burden applies); across domains, communication is message-passing (simpler
   abstraction).

   This file is axiom-free. *)

From Stdlib Require Import Bool ZArith List.
Require Import machine_types.
Require Import machine.

(* --- SSG-9 topology records --- *)

(* A NUMA node: a group of cores sharing node-local memory. *)
Record Node := {
  node_id    : Z;
  node_cores : list nat;       (* indices into Machine_cores *)
  node_mem_start : Z;
  node_mem_end   : Z
}.

(* A multikernel domain: a group of Nodes. *)
Record Domain := {
  dom_id    : Z;
  dom_nodes : list nat
}.

(* A topology partitions the flat Machine_cores into Nodes within Domains. *)
Record Topology := {
  topo_nodes   : list Node;
  topo_domains : list Domain;
  topo_node_mem : Z
}.

(* --- Topology queries --- *)

Fixpoint find_node (nodes : list Node) (nid : Z) : option Node :=
  match nodes with
  | nil => None
  | cons n rest =>
    if Z.eqb (node_id n) nid then Some n else find_node rest nid
  end.

Fixpoint find_domain (doms : list Domain) (did : Z) : option Domain :=
  match doms with
  | nil => None
  | cons d rest =>
    if Z.eqb (dom_id d) did then Some d else find_domain rest did
  end.

Fixpoint core_in_node (cores : list nat) (idx : nat) : bool :=
  match cores with
  | nil => false
  | cons c rest =>
    if Nat.eqb c idx then true else core_in_node rest idx
  end.

Fixpoint node_in_domain (nodes : list nat) (nid : nat) : bool :=
  match nodes with
  | nil => false
  | cons n rest =>
    if Nat.eqb n nid then true else node_in_domain rest nid
  end.

(* --- Topology invariants --- *)

Definition no_cross_domain_aliasing (topo : Topology) : Prop :=
  forall d1 d2 nid1 nid2,
    In d1 (topo_domains topo) ->
    In d2 (topo_domains topo) ->
    dom_id d1 <> dom_id d2 ->
    In nid1 (dom_nodes d1) ->
    In nid2 (dom_nodes d2) ->
    forall n1 n2,
      find_node (topo_nodes topo) (Z.of_nat nid1) = Some n1 ->
      find_node (topo_nodes topo) (Z.of_nat nid2) = Some n2 ->
      node_mem_start n1 >= node_mem_end n2 \/
      node_mem_start n2 >= node_mem_end n1.

(* --- Example topology: 2-node, 2-domain --- *)

Definition example_node0 : Node :=
  {| node_id := 0;
     node_cores := cons 0%nat (cons 1%nat nil);
     node_mem_start := 0;
     node_mem_end := 34359738368 |}.

Definition example_node1 : Node :=
  {| node_id := 1;
     node_cores := cons 2%nat (cons 3%nat nil);
     node_mem_start := 34359738368;
     node_mem_end := 68719476736 |}.

Definition example_domain0 : Domain :=
  {| dom_id := 0; dom_nodes := cons 0%nat nil |}.

Definition example_domain1 : Domain :=
  {| dom_id := 1; dom_nodes := cons 1%nat nil |}.

Definition example_topo : Topology :=
  {| topo_nodes := cons example_node0 (cons example_node1 nil);
     topo_domains := cons example_domain0 (cons example_domain1 nil);
     topo_node_mem := 68719476736 |}.

(* --- Test vectors --- *)

Lemma topo_find_node0 :
  find_node (topo_nodes example_topo) 0 = Some example_node0.
Proof. reflexivity. Qed.

Lemma topo_find_node1 :
  find_node (topo_nodes example_topo) 1 = Some example_node1.
Proof. reflexivity. Qed.

Lemma topo_find_node_unknown :
  find_node (topo_nodes example_topo) 99 = None.
Proof. reflexivity. Qed.

Lemma topo_find_domain0 :
  find_domain (topo_domains example_topo) 0 = Some example_domain0.
Proof. reflexivity. Qed.

Lemma topo_core0_in_node0 :
  core_in_node (node_cores example_node0) 0 = true.
Proof. reflexivity. Qed.

Lemma topo_core2_not_in_node0 :
  core_in_node (node_cores example_node0) 2 = false.
Proof. reflexivity. Qed.

Lemma topo_node0_in_domain0 :
  node_in_domain (dom_nodes example_domain0) 0 = true.
Proof. reflexivity. Qed.

Lemma topo_node1_not_in_domain0 :
  node_in_domain (dom_nodes example_domain0) 1 = false.
Proof. reflexivity. Qed.

Lemma topo_node_mem_disjoint :
  node_mem_end example_node0 <= node_mem_start example_node1.
Proof. reflexivity. Qed.

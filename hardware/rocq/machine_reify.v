(* Tessera — the pure machine reification shared by the S2.1 (HeapLang) and
   S2.2 (gpfsl) proofs.

   Both the sequential-consistency proof (shootdown_iris.v) and the weak-memory
   proof (shootdown_weak*.v) model the N-core broadcast as a Machine whose leaf
   PTE for `va` is invalid and whose cores reify their TLB state from a pending
   map.  This file is the *pure* part of that bridge — no iris/heap_lang, no
   gpfsl — so it is importable from both value models (HeapLang's nested-pair
   `val` and gpfsl's `LitPoison|LitLoc|LitInt`) without a notation clash.

   The only machine-level fact is [broadcast_reifies_machine], which cites
   `invalidate_shootdown_empty_cores` (shootdown.v) to conclude
   [Forall (translate = None /\ tlb_lookup = None)] on every core of the
   post-machine. *)

From stdpp Require Import gmap. (* gmap/dom and the ∈ notation *)
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Require Import machine_types.
Require Import machine.
Require Import machine_encoding. (* invalid_pte/valid_pte, leaf_entry, invalid_pte_not_valid *)
Require Import coherence_leaf.   (* invalidate_leaf_mem *)
Require Import shootdown.        (* core_with_root, invalidate_shootdown_empty_cores *)
Import ListNotations.

(* A core whose TLB is the reification of an [option TlbEntry]: [None] is an
   empty TLB, [Some e] is the singleton [e]. *)
Definition reify_core (root : mword 44) (o : option TlbEntry) : Core :=
  {| Core_satp_ppn := root; Core_tlb := match o with None => [] | Some e => [e] end;
     Core_hart := 0; Core_node := 0 |}.

(* Reconstructs the machine the broadcast program models: memory whose leaf PTE
   for `va` is `p` (written via the data-dependent walk), and n cores sharing
   `root` whose TLBs are reified from `tls`. *)
Definition reify_machine (root : mword 44) (va : mword 64) (mem : list MemEntry)
                        (p : Pte) (tls : nat -> option TlbEntry) (n : nat) : Machine :=
  {| Machine_mem := invalidate_leaf_mem (core_with_root root) mem va p;
     Machine_cores := List.map (fun j => reify_core root (tls j)) (seq 0 n);
     Machine_ram := [];
     Machine_ipi := [];
     Machine_iotlb := []; Machine_devtlbs := []; Machine_prireqs := []; Machine_ioqueue := []; Machine_stes := []; Machine_cds := [] |}.

(* Core [j] still caches the stale [leaf_entry va] exactly while it is pending
   (in the domain of the map [m]); once it has acked its TLB is empty.  The map's
   value type is irrelevant to the reification, hence the implicit [A]. *)
Definition tls_of {A} (va : mword 64) (m : gmap nat A) (j : nat) : option TlbEntry :=
  if decide (j ∈ dom m) then Some (leaf_entry va) else None.

(* The machine the broadcast program models before/after the shootdown. *)
Definition broadcast_pre_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) : Machine :=
  reify_machine root va mem valid_pte (fun _ => Some (leaf_entry va)) n.

Definition broadcast_post_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) : Machine :=
  reify_machine root va mem invalid_pte (fun _ => None) n.

(* The reified post-machine (every TLB cleared, leaf PTE invalid) satisfies the
   machine-level conclusion, citing `invalidate_shootdown_empty_cores`. *)
Lemma broadcast_reifies_machine (root : mword 44) (va : mword 64) (mem : list MemEntry) (n : nat) :
  Forall (fun c => translate c (broadcast_post_machine root va mem n).(Machine_mem) va = None /\
                   tlb_lookup c va = None)
         (broadcast_post_machine root va mem n).(Machine_cores).
Proof.
  apply (invalidate_shootdown_empty_cores root va mem n invalid_pte invalid_pte_not_valid).
Qed.

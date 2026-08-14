(* Tessera S2.2 smoke test — does the gpfsl/ORC11 weak-memory base import cleanly
   *alongside* the generated machine model (SailStdpp + machine_types + machine)?
   This is the reconciliation frontier for S2.2: if these two namespaces coexist
   without notation/instance clashes, the weak-memory shootdown proof can be written
   over the concrete machine. *)

From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import lifting proofmode.
From gpfsl.base_logic Require Import vprop.
From SailStdpp Require Import MachineWord.
Require Import machine_types.
Require Import machine.

(* A trivial definition that forces both namespaces to resolve and typecheck
   together: an identity on a machine [Pte], phrased as a gpfsl vProp is not needed
   yet — just making the imports and a machine-level term coexist suffices. *)
Definition s2_smoke_pte (p : Pte) : Pte := p.

Lemma s2_smoke_pte_id (p : Pte) : s2_smoke_pte p = p.
Proof. reflexivity. Qed.

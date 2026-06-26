(* Toolchain check: Iris bunched-implication logic + the proof mode. *)
From iris.proofmode Require Import proofmode.
From iris.bi Require Import bi.

Lemma sep_comm_test {PROP : bi} (P Q : PROP) : (P ∗ Q ⊢ Q ∗ P).
Proof. iIntros "[HP HQ]". iFrame. Qed.

Lemma wand_test {PROP : bi} (P Q : PROP) : (P ∗ (P -∗ Q) ⊢ Q).
Proof. iIntros "[HP HW]". iApply ("HW" with "HP"). Qed.

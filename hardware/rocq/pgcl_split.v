(* Tessera — pgcl failure-mode vectors #7 (THP split phantom `_mapcount`) and
   #8 (`__split_huge_zero_page_pmd` loop bound / RSS leak).

   These two catalogued bugs are *sequential* mapcount/RSS miscounts over the
   extent + PTE-vector, so — unlike #9/#10/#12 (which piggyback on the AArch64
   TLB variant in `aarch64_pgcl.v`) — they need their own sequential M1–M3
   split/mapcount model.  This file is that model, over plain lists of `Z`/`bool`
   (no Sail-generated types are involved: the bug lives in the software rmap
   accounting, not in the MMU encoding).

   Vocabulary (doc/failure-modes-pgcl.md):
     MMUPAGE_SIZE = M   (the hardware sub-page)
     PAGE_SIZE     = M << PAGE_MMUSHIFT   (the KAU = a cluster of
                        c = PAGE_MMUCOUNT sub-pages; one `struct page` per KAU)
     c = PAGE_MMUCOUNT = 1 << PAGE_MMUSHIFT   (the cluster factor)

   #7 (commits c30352064c4c / 7dcee907e3b5 / c7221b452105): when an anonymous
   mTHP folio is only *partially* mapped, `folio_add_new_anon_rmap()` bulk-inits
   `_mapcount = 0` for all c sub-pages while the fault path installs a single
   PTE.  `__split_folio_to_order()` (pre-fix) only reset sub-folios at idx > 0
   (and only under CONFIG_DEBUG_VM), so the head's phantom `_mapcount = 0`
   survived the split: `folio_mapped(head)` = true with no PTE referencing it,
   and the caller's `folio_put()` freed a folio that still self-reported as
   mapped — the free-while-mapped UAF (inv2/inv4, the brief's named "split/fold"
   heart).  The fix force-resets every post-split sub-folio to -1 and lets
   `remap_page()` inc back to 0 iff a migration entry exists.

   #8 (commit 8619b76a6f2c): `__split_huge_zero_page_pmd` iterated HPAGE_PMD_NR
   (32) times with a PAGE_SIZE stride instead of HPAGE_PMD_MMUNR (512) times
   with an MMUPAGE_SIZE stride, leaving 480 of 512 PTE slots `pte_none`; later
   faults on those empty slots created unbalanced RSS counter increments.

   What is proved here:
     * `split_correct` (the fixed `__split_folio_to_order`) yields the invariant
       "mapped iff a live PTE/migration entry references the sub-page" on every
       sub-page (`split_correct_sound`); the buggy split leaves the head
       phantom-mapped (`test_vector_pgcl7_*`).
     * the correct huge-zero-page split leaves zero `pte_none` slots, and the
       buggy one leaves `n_kau*(c-1)` of them — the RSS-leak slots — pinned with
       the commit's own 512/32/480 numbers as `vm_compute` vectors.

   See doc/failure-modes-pgcl.md (#7, #8). *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

(* ============================================================
   #7: THP split leaves a phantom head `_mapcount` (free-while-mapped).
   ============================================================ *)

(* One sub-page (a post-split order-0 folio, or a pre-split slot of the compound
   folio).  `_mapcount` follows the Linux convention: -1 = 0 mappings, 0 = 1
   mapping, n = n+1 mappings — so "mapped" is `_mapcount >= 0`.  `sp_has_pte`
   records whether a live PTE / migration entry references this sub-page. *)
Record SubPage := { sp_mapcount : Z; sp_has_pte : bool }.

Definition mapped_bool (s : SubPage) : bool := Z.leb 0%Z (sp_mapcount s).

(* A fresh compound folio: c sub-pages, all unmapped, no PTEs. *)
Definition fresh_folio (c : nat) : list SubPage :=
  List.repeat {| sp_mapcount := (-1)%Z; sp_has_pte := false |} c.

(* `folio_add_new_anon_rmap()`: bulk-initializes `_mapcount = 0` (the "1
   mapping" value) for *every* sub-page — the PGCL premise that makes the
   phantom possible when the fault path then installs only one PTE. *)
Definition add_new_anon_rmap_bulk (subs : list SubPage) : list SubPage :=
  List.map (fun s => {| sp_mapcount := 0%Z; sp_has_pte := sp_has_pte s |}) subs.

(* The fault path installs exactly one PTE at sub-page j. *)
Fixpoint install_pte (subs : list SubPage) (j : nat) : list SubPage :=
  match subs, j with
  | [], _        => []
  | s :: ss, O   => {| sp_mapcount := sp_mapcount s; sp_has_pte := true |} :: ss
  | s :: ss, S k => s :: install_pte ss k
  end.

(* `unmap_folio()` during `__folio_split`: decrement `_mapcount` only for the
   sub-page that carries a PTE (it becomes the migration entry); sub-pages that
   never had a PTE keep their (phantom) `_mapcount = 0`. *)
Definition unmap_folio (subs : list SubPage) : list SubPage :=
  List.map (fun s => if sp_has_pte s
                     then {| sp_mapcount := Z.sub (sp_mapcount s) 1%Z; sp_has_pte := true |}
                     else s) subs.

(* The fixed `__split_folio_to_order()`: force-reset every sub-folio to -1, then
   `remap_page()` restores `_mapcount = 0` iff a migration entry exists. *)
Definition split_correct (subs : list SubPage) : list SubPage :=
  List.map (fun s => if sp_has_pte s
                     then {| sp_mapcount := 0%Z; sp_has_pte := true |}
                     else {| sp_mapcount := (-1)%Z; sp_has_pte := false |}) subs.

(* The pre-fix split: no reset at all, so phantom `_mapcount`s survive. *)
Definition split_buggy (subs : list SubPage) : list SubPage := subs.

(* The invariant the split must maintain: "mapped" iff a live PTE/migration
   entry references the sub-page (inv4, consistent split). *)
Definition sound (subs : list SubPage) : bool :=
  forallb (fun s => Bool.eqb (mapped_bool s) (sp_has_pte s)) subs.

Definition head_mapcount (subs : list SubPage) : Z :=
  match subs with s :: _ => sp_mapcount s | [] => 0%Z end.

Definition head_has_pte (subs : list SubPage) : bool :=
  match subs with s :: _ => sp_has_pte s | [] => false end.

(* The phantom scenario: bulk-init, one PTE at sub-page j (j <> 0 = head), then
   unmap — the pre-split state the commit observes as rc=2 mc=1 order=4. *)
Definition phantom_folio (c j : nat) : list SubPage :=
  unmap_folio (install_pte (add_new_anon_rmap_bulk (fresh_folio c)) j).

(* The fixed split satisfies "mapped iff has_pte" for every sub-page. *)
Lemma split_correct_sound (subs : list SubPage) :
  Forall (fun s => mapped_bool s = sp_has_pte s) (split_correct subs).
Proof.
  induction subs as [| s ss IH]; cbn [split_correct List.map].
  - constructor.
  - constructor.
    + unfold mapped_bool. destruct (sp_has_pte s); cbn; reflexivity.
    + exact IH.
Qed.

(* ============================================================
   #8: `__split_huge_zero_page_pmd` loop bound leaves pte_none slots.
   ============================================================ *)

Inductive pte_state := pte_none | pte_zero | pte_present.

(* The correct split: populate every MMU-page slot (HPAGE_PMD_MMUNR = n_kau*c). *)
Definition huge_zero_split_correct (total : nat) : list pte_state :=
  List.repeat pte_zero total.

(* The buggy split: populate only HPAGE_PMD_NR = n_kau slots (1 per KAU),
   leaving the other n_kau*(c-1) slots pte_none. *)
Definition huge_zero_split_buggy (n_kau c : nat) : list pte_state :=
  List.repeat pte_zero n_kau ++ List.repeat pte_none (n_kau * c - n_kau).

Fixpoint count_pte_none (slots : list pte_state) : nat :=
  match slots with
  | [] => 0%nat
  | pte_none :: ps => S (count_pte_none ps)
  | _ :: ps        => count_pte_none ps
  end.

(* Each pte_none slot is a later fault that re-increments RSS: the leak is the
   number of slots the split failed to populate. *)
Definition rss_leak (slots : list pte_state) : Z := Z.of_nat (count_pte_none slots).

Lemma count_pte_none_app (a b : list pte_state) :
  count_pte_none (a ++ b) = count_pte_none a + count_pte_none b.
Proof.
  induction a as [| p ps IH]; cbn [app].
  - reflexivity.
  - destruct p; cbn [count_pte_none].
    + rewrite IH. lia.
    + exact IH.
    + exact IH.
Qed.

Lemma count_pte_none_repeat_zero (n : nat) :
  count_pte_none (List.repeat pte_zero n) = 0%nat.
Proof.
  induction n as [| k IH]; cbn [List.repeat count_pte_none].
  - reflexivity.
  - exact IH.
Qed.

Lemma count_pte_none_repeat_none (n : nat) :
  count_pte_none (List.repeat pte_none n) = n.
Proof.
  induction n as [| k IH]; cbn [List.repeat count_pte_none].
  - reflexivity.
  - f_equal. exact IH.
Qed.

(* The correct split leaves no pte_none slot. *)
Lemma huge_zero_split_correct_no_none (total : nat) :
  count_pte_none (huge_zero_split_correct total) = 0%nat.
Proof.
  unfold huge_zero_split_correct. apply count_pte_none_repeat_zero.
Qed.

(* The buggy split leaves exactly n_kau*(c-1) pte_none slots (480 for the
   commit's 32 KAUs of c=16). *)
Lemma huge_zero_split_buggy_none_count (n_kau c : nat) :
  count_pte_none (huge_zero_split_buggy n_kau c) = n_kau * c - n_kau.
Proof.
  unfold huge_zero_split_buggy.
  rewrite count_pte_none_app.
  rewrite count_pte_none_repeat_zero, count_pte_none_repeat_none.
  lia.
Qed.

(* ============================================================
   Executable vectors (vm_compute).
   ============================================================ *)

(* --- #7: the head phantom mapcount survives the buggy split, but not the
   fixed one.  c=4, PTE at sub-page 1 (a non-head sub-page). --- *)

Lemma test_vector_pgcl7_buggy_head_phantom :
  head_mapcount (split_buggy (phantom_folio 4 1)) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pgcl7_buggy_head_no_pte :
  head_has_pte (split_buggy (phantom_folio 4 1)) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pgcl7_buggy_unsound :
  sound (split_buggy (phantom_folio 4 1)) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pgcl7_correct_head_unmapped :
  head_mapcount (split_correct (phantom_folio 4 1)) = (-1)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pgcl7_correct_sound :
  sound (split_correct (phantom_folio 4 1)) = true.
Proof. vm_compute. reflexivity. Qed.

(* The commit's own configuration: order-4 mTHP (c=16 sub-pages). *)
Lemma test_vector_pgcl7_buggy_head_phantom_c16 :
  head_mapcount (split_buggy (phantom_folio 16 1)) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

(* --- #8: the loop bound leaves 480 of 512 slots pte_none (RSS leak). --- *)

Lemma test_vector_pgcl8_correct_no_none :
  count_pte_none (huge_zero_split_correct 512) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pgcl8_buggy_480_none :
  count_pte_none (huge_zero_split_buggy 32 16) = 480%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pgcl8_buggy_rss_leak :
  rss_leak (huge_zero_split_buggy 32 16) = 480%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma test_vector_pgcl8_correct_rss_leak :
  rss_leak (huge_zero_split_correct 512) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

(* A compact instance (2 KAUs of c=4 -> 6 of 8 slots left none). *)
Lemma test_vector_pgcl8_buggy_small_none :
  count_pte_none (huge_zero_split_buggy 2 4) = 6%nat.
Proof. vm_compute. reflexivity. Qed.

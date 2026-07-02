(* Tessera Property 2 / pgcl #143 task #21 — SWAP DEVICE slot accounting (the zram 16x over-count).

   Coq mirror of proof/Tessera/SwapDevice.lean.  A swap device of `bytes` capacity is carved
   into slots at the MMUPAGE (4KB) granule -- one swap slot per 4KB (folio_dup_swap;
   read_swap_header: swapfilepages = i_size >> MMUPAGE_SHIFT).  A 64KB cluster is MMUCOUNT (16)
   contiguous slots.  The correct slot count is bytes/MMUPAGE; the observed zram bug enabled
   MMUCOUNT x that (8GB device -> 128GB swap), over-committing the device.  Parametric (Coq's
   unary nat can't evaluate 8 GiB; the 8 GiB concrete case is in the Lean file). *)

Require Import Arith Lia Ring.

Definition MMUPAGE := 4096.
Definition MMUCOUNT := 16.
Definition CLUSTER := MMUPAGE * MMUCOUNT.

Record Dev := mkDev { bytes : nat }.

Definition slots (d : Dev) : nat := bytes d / MMUPAGE.
Definition slotsBug (d : Dev) : nat := MMUCOUNT * slots d.

Lemma mmupage_pos : MMUPAGE <> 0. Proof. unfold MMUPAGE; discriminate. Qed.

(* the over-count is exactly the cluster factor *)
Theorem slotsBug_is_16x d : slotsBug d = 16 * slots d.
Proof. reflexivity. Qed.

(* CORRECT FITS: the true slot count times the slot size equals the device capacity. *)
Theorem slots_fits d k (hk : bytes d = k * MMUPAGE) : slots d * MMUPAGE = bytes d.
Proof.
  unfold slots. rewrite hk. rewrite Nat.div_mul by exact mmupage_pos. reflexivity.
Qed.

(* THE BUG OVER-COMMITS: the 16x count claims MMUCOUNT x the device's real bytes -> the swap
   layer commits slots the device cannot hold -> writes past the end (corruption/OOM). *)
Theorem slotsBug_overcommits d k (hk : bytes d = k * MMUPAGE) (hpos : 0 < bytes d) :
  slotsBug d * MMUPAGE = 16 * bytes d /\ bytes d < slotsBug d * MMUPAGE.
Proof.
  assert (hf : slots d * MMUPAGE = bytes d) by (apply (slots_fits d k hk)).
  unfold slotsBug, MMUCOUNT.
  assert (key : 16 * slots d * MMUPAGE = 16 * bytes d).
  { replace (16 * slots d * MMUPAGE) with (16 * (slots d * MMUPAGE)) by ring.
    rewrite hf. reflexivity. }
  split; [ exact key | rewrite key; lia ].
Qed.

(* CORRECT NEVER over-commits (the contrast). *)
Theorem slots_no_overcommit d k (hk : bytes d = k * MMUPAGE) : slots d * MMUPAGE <= bytes d.
Proof. rewrite (slots_fits d k hk). lia. Qed.

(* CLUSTER-SLOT IDENTITY: a device of k clusters has exactly MMUCOUNT*k slots -- a per-cluster
   swap alloc/free (MMUCOUNT slots as one block) tiles the area with no remainder. *)
Theorem slots_eq_clusters_scaled d k (hk : bytes d = k * CLUSTER) : slots d = MMUCOUNT * k.
Proof.
  unfold slots. rewrite hk. unfold CLUSTER.
  replace (k * (MMUPAGE * MMUCOUNT)) with ((k * MMUCOUNT) * MMUPAGE) by ring.
  rewrite Nat.div_mul by exact mmupage_pos. ring.
Qed.

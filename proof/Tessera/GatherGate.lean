/-
  Tessera — the GATHER-OWES RE-HOLD GATE (#143 reincarnation band-aid, QEMU-validated 2026-07-02).

  The full structural fix is Route 2 (`GatherLedger`: make every mapping ref genuine so the gather's
  deferred put is `Deferred.Pinned` by construction).  This models the lower-risk INTERIM that QEMU
  showed closes the reincarnation with no leak: when a NON-gather freer (reclaim's vmscan
  free_unref_folios, or an lru_add drain from fadvise, or a cross-mm aggregate over-put) would drop a
  folio's refcount to 0 WHILE an mmu_gather still OWES a deferred put on it (pgcl143_gather_owes stamp
  set), RE-HOLD it -- kernel `folio_ref_inc(folio); continue;` in free_unref_folios (the chokepoint
  reclaim funnels through) and folios_put_refs.  The folio stays live until the OWING gather's own
  discharge -- which runs with pgcl143_in_gflush set, so it is NOT gated, and clears the owe first
  (mmu_gather.c) -- frees it exactly once.

  The point: the reincarnation UAF is "the racer frees the owed folio to 0, then the gather's deferred
  put double-frees the reincarnated frame."  The gate makes the racer's drop a NO-OP-on-free while
  owed, so ONLY the owing gather frees, exactly once -- no double-free, hence no freelist `list_add`
  corruption, hence no pcp-lock wedge.  Cost is a re-hold that leaks only if the owe never discharges
  (leak-beats-corruption); QEMU showed 0 OOM over 200s.
-/
namespace Tessera
namespace GatherGate

/-- A folio's free-state: `refs` currently held; `owed` = an mmu_gather still owes it a deferred put
(the `pgcl143_gather_owes[pfn] == pfn` stamp). -/
structure Owed where
  refs : Nat
  owed : Bool
deriving Repr, DecidableEq

/-- freed = the refcount reached 0 (the page goes to the pcp/buddy freelist). -/
def Owed.freed (s : Owed) : Prop := s.refs = 0

/-- UNGATED racer drop (pre-fix): a non-gather freer drops one ref and frees at 0 regardless of `owed`. -/
def Owed.racerDrop (s : Owed) : Owed := { s with refs := s.refs - 1 }

/-- **THE BUG (reincarnation):** the ungated racer drop of an OWED, singly-held folio frees it WHILE
the gather still owes it — so the gather's later deferred put double-frees the reincarnated frame. -/
theorem racer_frees_while_owed :
    (Owed.racerDrop ⟨1, true⟩).freed ∧ (⟨1, true⟩ : Owed).owed = true :=
  ⟨rfl, rfl⟩

/-- The GATED racer drop (the fix): if the folio is OWED and this drop would free it (`refs = 1`),
RE-HOLD — leave `refs` unchanged, skip the free; otherwise drop normally. -/
def Owed.gatedDrop (s : Owed) : Owed :=
  if s.owed = true ∧ s.refs = 1 then s else { s with refs := s.refs - 1 }

/-- **THE GATE IS SOUND:** a gated racer drop NEVER frees an owed (live) folio — it stays live for the
owing gather's discharge, for any hold count. -/
theorem gate_never_frees_while_owed (s : Owed) (ho : s.owed = true) (hlive : 0 < s.refs) :
    ¬ (Owed.gatedDrop s).freed := by
  unfold Owed.gatedDrop
  by_cases h1 : s.refs = 1
  · rw [if_pos ⟨ho, h1⟩]; show ¬ (s.refs = 0); omega
  · rw [if_neg (fun h => h1 h.2)]; show ¬ (s.refs - 1 = 0); omega

/-- The owing gather's own discharge: `pgcl143_in_gflush` is set, so it is NOT gated (it clears the
owe first in mmu_gather.c, then frees).  It drops its owed ref and clears the stamp. -/
def Owed.discharge (s : Owed) : Owed := { refs := s.refs - 1, owed := false }

/-- **EXACTLY ONCE:** after the racer is re-held, the owing gather's discharge frees the folio (once)
and leaves it un-owed — no second (double) free, because the racer never freed it. -/
theorem gate_then_discharge_frees_once :
    (Owed.discharge (Owed.gatedDrop ⟨1, true⟩)).freed ∧
    (Owed.discharge (Owed.gatedDrop ⟨1, true⟩)).owed = false :=
  ⟨rfl, rfl⟩

/-- Contrast — the gate does NOT change behaviour for an UN-owed folio: a racer drop frees it normally
(no leak of legitimate frees; the gate fires only while a gather owes). -/
theorem gate_frees_unowed_normally :
    (Owed.gatedDrop ⟨1, false⟩).freed :=
  rfl

end GatherGate
end Tessera

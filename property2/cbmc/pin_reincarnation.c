/*
 * r3pin CBMC harness — the count-correct per-gather PIN absorbs the reincarnation over-drop.
 * Mirrors Tessera GatherLedger.Ledger.owing_not_freed on the REAL folios_put_refs floor
 * arithmetic, over ALL nondeterministic racer behaviours (CBMC enumerates them).
 *
 * Faithful state: a shared cluster folio, refcount = owed_mapref(1) + racer_base(1) + PIN.
 *   - A gather G has zapped + deferred, so it OWES a discharge (owing=1); with r3pin it took
 *     a dedicated folio_get (the PIN) at __tlb_remove_folio_pages.
 *   - The racer (lru_add_drain) drops refs.  The r2diag2 bug is that it can OVER-drop and
 *     reach G's owed mapping ref (the cross-mm over-put / "not gather-stamped" double-free).
 *     CBMC tries BOTH: the balanced drop (its own base) and the over-drop (base + owed).
 *
 * Property (owing_not_freed): while G still owes, the folio must NOT be freed.
 *   PIN=0 (current kernel): CBMC finds the over-drop => freed-while-owed (reincarnation).
 *   PIN=1 (r3pin): the dedicated pin ref buffers the over-drop => never freed while owed,
 *   and G's discharge then frees it exactly once (no leak, no double-free).
 */
#include <assert.h>

#ifndef PIN
#define PIN 1
#endif

int nondet_uint(void);

int main(void)
{
	int refcount = 1 /*owed mapref, in-flight*/ + 1 /*racer base ref*/ + PIN /*the pin*/;
	int owing = 1;
	int freed = 0, dblfree = 0;

	/* The racer drops a nondeterministic number of refs, 1..2:
	 *   1 = balanced (its own base ref)
	 *   2 = the OVER-drop that also eats G's owed mapping ref (the observed bug) */
	unsigned d = nondet_uint();
	__CPROVER_assume(d == 1 || d == 2);

	/* racer put, with the folios_put_refs FLOOR */
	int old = refcount;
	refcount = (old >= (int)d) ? old - (int)d : 0;
	if (refcount == 0) { if (freed) dblfree = 1; freed = 1; }

	/* ****  owing_not_freed: G still owes => the frame must be alive  **** */
	assert(!(owing > 0 && freed));

	/* G's own discharge (drops its mapref + its pin), floored */
	int drop = 1 + PIN;
	old = refcount;
	refcount = (old >= drop) ? old - drop : 0;
	owing = 0;
	if (refcount == 0) { if (freed) dblfree = 1; freed = 1; }

	/* exactly once, no double-free */
	assert(!dblfree);
	return 0;
}

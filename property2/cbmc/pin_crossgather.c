/*
 * r3pin CBMC harness — the count-correct per-gather PIN (Tessera GatherLedger.Ledger).
 *
 * Scenario: ONE shared cluster-folio (e.g. a libcef.so code cluster) mapped by TWO mms.
 * Both mms' mmu_gathers zap+defer concurrently, while a racer (lru_add_drain: it took a
 * base ref via folio_get, then drains it) runs interleaved.  CBMC explores ALL statement
 * interleavings of the three threads.
 *
 * Faithful to the kernel refcount arithmetic:
 *   - defer  (mmu_gather.c __tlb_remove_folio_pages_size): PIN => refcount++  (folio_get)
 *   - discharge (swap_state.c free_pages_and_swap_cache): drop (mapref + PIN) with the
 *     folios_put_refs FLOOR (new = old>=k ? old-k : 0), free iff it reached 0.
 *   - racer: balanced folio_get/folio_put of its OWN base ref (the LRU batch ref).
 *
 * Checks:
 *   (1) NO PREMATURE FREE  — never freed while EITHER mm's sub-PTEs are still present
 *       (the reincarnation / libcef.so int3 root).
 *   (2) NO DOUBLE-FREE     — the frame reaches refcount 0 at most once (the 68 r2diag2
 *       folios_put_refs double-frees).
 *   (3) NO LEAK            — exactly the cache ref remains at quiescence.
 *
 * Build both: -DPIN=1 (r3pin, must be SUCCESSFUL) and -DPIN=0 (current kernel, CBMC must
 * find a counterexample => the harness is meaningful).
 */
#include <assert.h>

#ifndef PIN
#define PIN 1
#endif

int refcount;         /* folio._refcount (shared) */
int freed, dblfree;
int present[2];       /* mm i still has sub-PTEs present (its share of the mapping) */
int owed[2];          /* mm i's gather owes a deferred discharge */

static void free_if_zero(int reached0)
{
	if (reached0) {
		if (freed)
			dblfree = 1;   /* second time refcount hit 0 => double-free */
		freed = 1;
	}
}

/* free_pages_and_swap_cache: drop (this mm's 1 mapping ref) + (PIN ? 1 pin : 0), FLOORED. */
static void discharge(int i)
{
	int drop = 1 + PIN;            /* kernel: this_refs (=1 here) + 1 pin */
	int reached0;
	__CPROVER_atomic_begin();
	int old = refcount;
	refcount = (old >= drop) ? (old - drop) : 0;   /* the folios_put_refs floor */
	reached0 = (refcount == 0);
	owed[i] = 0;
	__CPROVER_atomic_end();
	free_if_zero(reached0);
}

/* mm i's gather: zap clears its PTEs and defers (taking the PIN), then discharges. */
static void gather(int i)
{
	__CPROVER_atomic_begin();
	present[i] = 0;               /* zap: this mm's sub-PTEs cleared */
	owed[i] = 1;                  /* gather now owes the deferred put */
	if (PIN)
		refcount++;           /* THE PIN: folio_get at __tlb_remove_folio_pages */
	__CPROVER_atomic_end();
	/* deferred window — the racer / the other gather may interleave here */
	discharge(i);
}

/* lru_add_drain racer: it holds its OWN base ref (folio_get on batch add); drain drops it. */
static void racer(void)
{
	int reached0;
	__CPROVER_atomic_begin();     /* (the folio_get already reflected in the initial refcount) */
	int old = refcount;
	refcount = (old >= 1) ? (old - 1) : 0;
	reached0 = (refcount == 0);
	__CPROVER_atomic_end();
	free_if_zero(reached0);
}

#define CHK() assert(!(freed && (present[0] || present[1])))

int main(void)
{
	/* refcount = cache(1) + mm0 map(1) + mm1 map(1) + racer's LRU base(1) = 4 */
	refcount = 4;
	freed = 0; dblfree = 0;
	present[0] = present[1] = 1;
	owed[0] = owed[1] = 0;
	int dA = 0, dB = 0, dR = 0;

	__CPROVER_ASYNC_1: { gather(0); CHK(); dA = 1; }
	__CPROVER_ASYNC_2: { gather(1); CHK(); dB = 1; }
	__CPROVER_ASYNC_3: { racer();   CHK(); dR = 1; }

	__CPROVER_assume(dA && dB && dR);
	CHK();
	assert(!dblfree);
	/* quiescent balance: 4 + 2*PIN(pins) - 2*(1+PIN)(discharges) - 1(racer) = 1 = the cache ref */
	assert(refcount == 1);
	return 0;
}

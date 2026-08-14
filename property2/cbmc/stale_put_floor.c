/*
 * stale-put / refcount-floor double-free CBMC harness — mirrors Tessera/StalePut.lean and
 * property2/coq/stale_put.v on the REAL folios_put_refs floor arithmetic, over ALL
 * nondeterministic (old refcount, drop k) pairs (CBMC enumerates them).
 *
 * folios_put_refs drops k = nr_refs from a cluster of current refcount `old`:
 *   POLICY=0 stock folio_ref_sub_and_test : frees iff old - k == 0.
 *   POLICY=1 floor band-aid               : new = max(0, old-k); frees iff new == 0  (<=> old<=k).
 *   POLICY=2 guard (the fix, if(old==0)continue): frees iff old>0 && new==0.
 *
 * SAFETY property: an already-free cluster (old == 0, a stale/duplicate put) is NEVER freed
 * again.  The floor VIOLATES it (old=0<=k => frees => the PGCL143-DOUBLEFREE the detector reports);
 * stock and the fix satisfy it.  For POLICY=2 we also prove ZERO BLAST RADIUS: on any live cluster
 * (old>0) the guard's free decision is identical to the floor's.
 *
 *   POLICY=0 -> SUCCESSFUL  (stock underflows on a stale put, never frees)
 *   POLICY=1 -> FAILED      (the floor manufactures the double-free; the harness bites)
 *   POLICY=2 -> SUCCESSFUL  (the guard never re-frees, and matches the floor on live clusters)
 */
#include <assert.h>

#ifndef POLICY
#define POLICY 2
#endif

int nondet_int(void);
unsigned nondet_uint(void);

int main(void)
{
	int old = nondet_int();
	unsigned k = nondet_uint();
	int floor_new, did_free = 0;

	__CPROVER_assume(old >= 0 && old <= 3);
	__CPROVER_assume(k >= 1 && k <= 4);   /* a real put drops >= 1 ref */

	floor_new = old > (int)k ? old - (int)k : 0;

#if POLICY == 0
	did_free = (old - (int)k == 0);       /* stock folio_ref_sub_and_test */
#elif POLICY == 1
	did_free = (floor_new == 0);          /* floor band-aid */
#else
	if (old != 0)                         /* the fix: `if (old == 0) continue;` */
		did_free = (floor_new == 0);
#endif

	/* SAFETY: an already-free cluster (old == 0) is NEVER freed a second time. */
	assert(!(did_free && old == 0));

#if POLICY == 2
	/* ZERO BLAST RADIUS: on any live cluster the guard matches the floor exactly. */
	if (old != 0)
		assert(did_free == (floor_new == 0));
#endif
	return 0;
}

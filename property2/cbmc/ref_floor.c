/*
 * REFCOUNT CORRECTIVE FLOOR (r14reffloor) CBMC harness -- mirrors Tessera/RefFloor.lean and
 * property2/coq/ref_floor.v over ALL nondeterministic (rc, mc, k) with the pre-put invariant mc<=rc
 * (r12fix keeps folio_mapcount honest, so rc>=mc holds before the put).
 *
 * rc = folio refcount; mc = honest folio_mapcount; k = nr_refs this put drops.  A still-mapped
 * folio (mc>0) must never be freed (refcount reaching 0).
 *
 *   FIX=0 (stock pgcl 0-floor) -> FAILED: CBMC finds an over-put (k>=rc) that drives rc to 0 while
 *          mc>0 -- the free-while-referenced (PGCL143-OVERPUT / env-page reuse).
 *   FIX=1 (r14 corrective floor: clamp at mc) -> SUCCESSFUL: rc never drops below mc, so a mapped
 *          folio is never freed; mc==0 leaves the 0-floor intact so the last put still frees.
 */
#include <assert.h>

#ifndef FIX
#define FIX 1
#endif

int nondet_int(void);

int main(void)
{
	int rc = nondet_int(), mc = nondet_int(), k = nondet_int();
	int new_refs;

	__CPROVER_assume(rc >= 0 && mc >= 0 && k >= 1);
	__CPROVER_assume(mc <= rc);		/* invariant holds before the put (mc honest, rc>=mc) */

	new_refs = (k <= rc) ? rc - k : 0;	/* the pgcl 0-floor */
#if FIX
	if (mc > 0 && new_refs < mc)		/* r14: never drop the refcount below the mappings */
		new_refs = mc;
#endif

	/* SAFETY: a still-mapped folio (mc>0) is never freed (new_refs==0). */
	assert(!(mc > 0 && new_refs == 0));
	return 0;
}

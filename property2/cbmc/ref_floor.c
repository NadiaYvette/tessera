/*
 * REFCOUNT CORRECTIVE FLOOR (r14reffloor + r16owefloor) CBMC harness -- mirrors
 * Tessera/RefFloor.lean and property2/coq/ref_floor.v over ALL nondeterministic (rc, mc, k, owed)
 * with the pre-put invariant mc<=rc (r12fix keeps folio_mapcount honest, so rc>=mc holds before
 * the put).
 *
 * rc = folio refcount; mc = honest folio_mapcount; k = nr_refs this put drops; owed = the
 * mmu_gather still owes a put on this folio (tracked in pgcl143_gather_owes[]).  TWO folios must
 * never be freed (refcount reaching 0): a still-mapped one (mc>0) and a gather-owed one (owed).
 *
 *   FIX=0 (stock pgcl 0-floor) -> FAILED: CBMC finds an over-put (k>=rc) that drives rc to 0 while
 *          mc>0 (free-while-referenced, PGCL143-OVERPUT) OR while owed (the reincarnation face:
 *          an UNMAPPED owed folio freed-to-buddy, __vmalloc-reincarnated, then stale-freed).
 *   FIX=1 (r14 mc-floor + r16 owe-floor: clamp at max(mc, owed?1:0)) -> SUCCESSFUL: rc never drops
 *          below the mappings NOR below 1 while owed; only an unmapped, un-owed folio still frees.
 */
#include <assert.h>

#ifndef FIX
#define FIX 1
#endif

int nondet_int(void);

int main(void)
{
	int rc = nondet_int(), mc = nondet_int(), k = nondet_int(), owed = nondet_int();
	int new_refs, floor;

	__CPROVER_assume(rc >= 0 && mc >= 0 && k >= 1);
	__CPROVER_assume(mc <= rc);		/* invariant holds before the put (mc honest, rc>=mc) */
	__CPROVER_assume(owed == 0 || owed == 1);

	new_refs = (k <= rc) ? rc - k : 0;	/* the pgcl 0-floor */
#if FIX
	floor = mc;				/* r14: never drop the refcount below the mappings */
	if (owed && floor < 1)			/* r16: nor below 1 while the gather still owes it */
		floor = 1;
	if (floor > 0 && new_refs < floor)
		new_refs = floor;
#endif

	/* SAFETY r14: a still-mapped folio (mc>0) is never freed (new_refs==0). */
	assert(!(mc > 0 && new_refs == 0));
	/* SAFETY r16: a gather-owed folio is never freed -> cannot be reincarnated + stale-freed. */
	assert(!(owed && new_refs == 0));
	return 0;
}

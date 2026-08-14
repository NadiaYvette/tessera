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

	/*
	 * ---- r19: the gather defers only the refs for the mappings it ACTUALLY removed ----
	 * r18 floored the mapcount removal to `own` edges but left the refcount deferral at the batch
	 * size nr >= own.  At discharge it dropped nr refs on a folio whose refcount was own+other
	 * (OTHER owners -- page cache / a pin / another gather -- hold `other`), over-dropping by
	 * nr-own into `other` -> that data page freed while still referenced (the OVERPUT deficit,
	 * mapcount=0, in_gflush=1 -> the renderer SIGSEGV).  Defer exactly `own`.  Mirrors
	 * RefFloor.deferDrop.
	 */
	{
		int own = nondet_int(), other = nondet_int(), nr = nondet_int();
		int rc2, drop, res2;

		__CPROVER_assume(own >= 0 && other >= 0 && nr >= own);
		__CPROVER_assume(own <= 1000000 && other <= 1000000 && nr <= 1000000);
		rc2 = own + other;		/* gather owns `own`; other owners hold `other` */
#if FIX
		drop = own;			/* r19: defer only what the gather owns */
#else
		drop = nr;			/* stock: defer the batch size nr >= own -- over-drops */
#endif
		res2 = (drop <= rc2) ? rc2 - drop : 0;

		/* SAFETY r19: the other owners' refs are never dropped -> no free-while-referenced. */
		assert(res2 >= other);
	}

	/*
	 * ---- r20: a still-cached file/shmem folio is never freed by a stale/cross-gather over-drop ----
	 * The r16 owe-floor excludes in_gflush, so two gathers both discharging a shared cluster
	 * (in_gflush on BOTH) over-drop unfloored (r19: same pfn 0x52e01 dropped 7->0 then 0-again).
	 * A provable over-drop (nr > rc) of a still-CACHED file/shmem folio (mapping!=NULL holds a cache
	 * ref; all r19 OVERPUT were anon=0) floors at 1 (the cache ref) even on the gather's own
	 * discharge.  Mirrors RefFloor.cacheFloor.
	 */
	{
		int rc3 = nondet_int(), nr3 = nondet_int(), cached = nondet_int();
		int res3;

		__CPROVER_assume(rc3 >= 0 && nr3 >= 0 && rc3 <= 1000000 && nr3 <= 1000000);
		__CPROVER_assume(cached == 0 || cached == 1);

		res3 = (rc3 > nr3) ? rc3 - nr3 : 0;	/* the 0-floor put */
#if FIX
		if (cached && nr3 > rc3)		/* r20: over-drop of a cached folio -> keep the cache ref */
			res3 = 1;
#endif
		/* SAFETY r20: a still-cached folio is never freed (res==0) by a provable over-drop. */
		assert(!(cached && nr3 > rc3 && res3 == 0));
	}
	return 0;
}

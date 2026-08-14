/*
 * reincarnation quarantine coverage CBMC harness — mirrors Tessera/Quarantine.lean and
 * property2/coq/quarantine.v.  A pfn a mmu_gather still OWES a deferred put for is freed by a
 * concurrent path; whether it reincarnates (reaches the buddy freelist while owed) depends on
 * whether the guard covers the free PATH.  CBMC enumerates every path.
 *
 *   UNIVERSAL=1 (the fix, __free_pages_prepare chokepoint) -> SUCCESSFUL: every path gated, an
 *               owed pfn never reincarnates.
 *   UNIVERSAL=0 (the bug, free_unref_folios folio-batch-only gate) -> FAILED: CBMC finds an
 *               off-path free (vfree / page-table RCU / alloc_exact) that reincarnates the pfn.
 */
#include <assert.h>

#ifndef UNIVERSAL
#define UNIVERSAL 1
#endif
#define FOLIO_BATCH 0   /* the one path the partial gate covers */

int nondet_int(void);

int main(void)
{
	int owed = 1;                  /* a mmu_gather owes a deferred put for this pfn */
	int reusable = 0;              /* on the buddy freelist -> re-handed-out (reincarnation) */
	unsigned path = nondet_int();  /* which free path frees it (folio-batch, vfree, ptbl, ...) */
	int gated;

	__CPROVER_assume(path <= 5);

#if UNIVERSAL
	gated = 1;                     /* __free_pages_prepare: EVERY path funnels through it */
#else
	gated = (path == FOLIO_BATCH); /* free_unref_folios: only the folio-batch path */
#endif

	if (owed && !gated)
		reusable = 1;          /* freed while owed via an ungated path -> reincarnation */

	/* SAFETY: an owed pfn must never become reusable (reincarnate) before discharge. */
	assert(!(owed && reusable));
	return 0;
}

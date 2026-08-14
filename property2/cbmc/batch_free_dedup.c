/*
 * batched-free cluster dedup CBMC harness — mirrors Tessera/BatchFree.lean and
 * property2/coq/batch_free.v on the REAL free_pages_and_swap_cache dedupe scan, over ALL
 * nondeterministic batch arrangements (CBMC enumerates them).
 *
 * A pgcl cluster is ONE struct page over PAGE_MMUCOUNT sub-units; a batched free may enqueue the
 * same cluster once per sub-unit it touched.  Per-ENTRY free (DEDUP=0) frees the struct page once
 * per entry -> a cluster listed twice is freed twice (the tlb_remove_table_rcu / shrink_folio_list
 * / folios_put_refs double-free).  The dedupe (DEDUP=1) coalesces same-cluster entries (the
 * free_pages_and_swap_cache scan) -> each distinct cluster is freed EXACTLY once.
 *
 *   DEDUP=0 -> FAILED      (CBMC finds a duplicated cluster => freed twice; the harness bites)
 *   DEDUP=1 -> SUCCESSFUL  (dedupe: no double-free, and no leak — every present cluster freed once)
 */
#include <assert.h>

#ifndef DEDUP
#define DEDUP 1
#endif
#define N 3          /* batch entries */
#define C 2          /* distinct cluster ids the entries may name */

int nondet_int(void);

int main(void)
{
	int id[N];
	int freed[C];
	int i, j, dblfree = 0;

	for (i = 0; i < C; i++)
		freed[i] = 0;
	for (i = 0; i < N; i++) {
		id[i] = nondet_int();
		__CPROVER_assume(id[i] >= 0 && id[i] < C);
	}

	for (i = 0; i < N; i++) {
		int emit = 1;
#if DEDUP
		/* free_pages_and_swap_cache dedupe: an earlier entry already named this
		 * cluster => fold into it, do not free again. */
		for (j = 0; j < i; j++)
			if (id[j] == id[i]) { emit = 0; break; }
#endif
		if (emit) {
			if (freed[id[i]])
				dblfree = 1;   /* this struct page freed a 2nd time */
			freed[id[i]] = 1;
		}
	}

	/* SAFETY: no cluster is ever freed twice. */
	assert(!dblfree);
	/* COMPLETENESS (no leak): every cluster that appears is freed. */
	for (i = 0; i < N; i++)
		assert(freed[id[i]] == 1);
	return 0;
}

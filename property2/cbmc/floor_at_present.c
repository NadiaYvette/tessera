/*
 * FLOOR-AT-PRESENT corrective floor (r12fix) + free-while-mapped gate (r13refgate) CBMC harness --
 * mirrors Tessera/FloorAtPresent.lean and property2/coq/floor_at_present.v over ALL nondeterministic
 * (rmap, present) start states (CBMC enumerates them, INCLUDING the over-removed rmap<present the
 * r11probe diagnostics caught).
 *
 * rmap = folio_mapcount; present = present_here (sub-PTEs of this cluster still present in this
 * table).  The invariant a faithful counter satisfies is present <= rmap (so folio_mapped() is
 * honest for a mapped cluster).
 *
 *   FIX=0 (old floor: SKIP a would-underflow remove, never repair) -> FAILED: CBMC finds an
 *          already-over-removed start (rmap < present) the skip leaves violated (present > rmap).
 *   FIX=1 (r12fix corrective floor: also CORRECT rmap up to present) -> SUCCESSFUL: present <= rmap
 *          restored from ANY start; and the r13refgate free-gate then frees only when present==0.
 */
#include <assert.h>

#ifndef FIX
#define FIX 1
#endif

int nondet_int(void);

int main(void)
{
	int rmap = nondet_int(), present = nondet_int();
	int r, p;

	__CPROVER_assume(present >= 0);		/* present_here is a count */

	r = rmap; p = present;
	if (p < r)				/* room: real floored remove (rmap drops) */
		r = r - 1;			/* r > p >= 0, so no underflow */
#if FIX
	else if (r < p)				/* r12fix: correct the undercount up to present */
		r = p;
#endif
	/* else hold */

	/* SAFETY: present <= rmap is restored (FIX) / only-maintained-if-faithful (old). */
	assert(p <= r);

	/* r13refgate free-gate: honest rmap => a free (gated on rmap==0) happens only when unmapped. */
	if (p <= r && r == 0)
		assert(p == 0);			/* no free-while-mapped */
	return 0;
}

# #143 worklog: reclaim stale-TLB lead (QEMU dangle-oracle session)

Date: 2026-06-30

## Reproducible signal (TCG, instrumented QEMU)

Full detector suite (`PGCL_DANGLE` + `PGCL_TLBSCAN` + `PGCL_RCHIST`) on the
`drive/143-bisect` kernel (count-correct swap free + swap sub-index carry, *no*
COW flush), 8-vCPU TCG, 2 GiB, ran to 614 s guest:

- **opcode faults: 127** (kill-init signature reproduced)
- **bad pages: 0** — no page-allocator "Bad page" dumps under TCG, so the
  `dump_page` post-mortem (leaf `0x51430004`) never fired; cross-mm `PM-walk`
  has no data this run.
- **FREE-WHILE-USER-MAPPED (`PGCL143tlbscan`): 64 catches**, *all*:
  - `pte_maps_frame=0` — PTE cleared by the unmap; the TLB entry survives =
    **stale-TLB**, not a present-dangler.
  - `writable=0` — read-only ⇒ **code/text pages**.
  - `cpu=1` / `cpu=5`, consecutive MMUPAGE-granular USER vas (`0x74bc303c0000`+).
- **free-site (`PGCL143freepath`): `shrink_folio_list (+0xc75)`** — reclaim/swap-out.
- **reuse-site (`PGCL143allocpath`): `get_page_from_freelist` /
  `__alloc_pages_slowpath` / `alloc_pages_mpol`** — a normal page allocation
  reuses the freed-but-still-TLB-mapped frame (the UAF setup).

## Candidate mechanism

`shrink_folio_list → try_to_unmap → try_to_unmap_one` clears all `nr_mmupages`
sub-PTEs of a cluster and records a deferred batch flush
(`set_tlb_ubc_flush_pending`, range `[address, address+nr*MMUPAGE_SIZE)`). The
unmap and the flush *range* are correct (full cluster); `try_to_unmap_flush`
runs before `free_unref_folios`. Yet a read-only code-page sub-TLB survives on
cpu1/cpu5 at the buddy free, and `get_page_from_freelist` then reuses the frame
⇒ the stale entry maps the reused frame ⇒ execute wrong code ⇒ invalid opcode
⇒ init death.

## The flush path is NOT a TCG artifact

`arch_tlbbatch_flush`: `TLB_FLUSH_ALL` over `batch->cpumask`, *or*
`invlpgb_flush_all_nonglobals()` if `X86_FEATURE_INVLPGB`. This QEMU does **not**
model INVLPGB and the dev host (i7-1370P) is Intel (no INVLPGB — that's AMD
Zen5); if the laptop is Intel or pre-Zen5 AMD it's the same. So KVM *and* TCG
take `flush_tlb_multi(batch->cpumask)` — the same path. The 64 catches are the
real cpumask flush path, not an INVLPGB emulation gap.

## Open question (the crux)

`batch->cpumask` = OR of `mm_cpumask(mm)`. A stale entry survives on a CPU only
if that CPU is **not** in `mm_cpumask` at flush time (lazy-TLB / PCID-tagged).
On real HW such entries are normally flushed by the per-mm `tlb_gen` comparison
on the next `switch_mm` (full flush on gen mismatch ⇒ pgcl-safe). So the catch
("live at free") is **necessary but not sufficient** for the UAF — it does not
prove the entry is *accessed* before the switch-back flush. Three possibilities:
(a) a real race where the consuming CPU touches the va before switch-back;
(b) a pgcl `tlb_gen`/`switch_mm` sub-frame gap; (c) benign lazy entries the
detector flags but HW handles.

## Confounds / limits

- **COW fix amplified, not fixed**: `flush_tlb_mm` in `wp_page_copy` cleared its
  COW catch but *amplified* the init-death (8.4 s) — consistent with reclaim
  being a downstream bug revealed by fixing COW ("a fix may reveal a downstream
  bug").
- **No mapcount divergence**: `xck-summary` reports `inuse=2 undercount=0
  overcount=0 freed_while_mapped=0`. The bug is not a struct-page mapcount
  accounting error.
- **Reader blind on the workload range**: `pgcl_read_page` is READER-OK for cpfn
  `0x10`/`0x20` but READ-FAIL for cpfn ≥ `0x40` (the whole workload range), so
  `PGCL143rchist` (rc/mc RIP over-put trajectory) and the read-based post-mortem
  are blind for workload clusters. The QEMU reader's vmemmap base needs
  calibration before those detectors are usable here.

## Next steps

1. **Confirm harm**: instrument the *access* (a TLB hit to a freed-but-mapped
   frame), or force a broadcast flush after the reclaim batch for pgcl clusters
   and see if the kill-init drops — minding the COW-flush amplification surprise.
2. **Calibrate** `pgcl_read_page`'s vmemmap base so RCHIST over-put detection
   works on the workload range.
3. **Audit** `switch_mm_irqs_off` / `tlb_gen` for pgcl sub-frame coverage.
4. **KVM cross-check** — the detectors are TCG-only; need an alternate signal on
   KVM (and ultimately the laptop).

## Detector recipe

```
env PGCL_DANGLE=1 PGCL_TLBSCAN=1 PGCL_RCHIST=1 PGCL_HISTGB=2 PGCL_HISTFILE=... \
  qemu-system-x86_64 -accel tcg -cpu max -smp 8 -m 2G ...
```

- markers: `PGCL143tlbscan` (FREE-WHILE-USER-MAPPED), `PGCL143freepath`/
  `allocpath` (stacks), `PGCL143PM-walk` (cross-mm pgd USER-PTE count, needs bad
  pages), `PGCL143rchist` (rc/mc RIP trajectory, needs reader), `PGCL143xck-
  summary` (PTE-tally vs mapcount), `PGCL143pgread` (reader self-test).
- kernel emitters: `pgcl143_qsig` (free/alloc `0x51430000|freed`, page_alloc.c),
  `dump_page` (`0x51430004`, debug.c) — both gated by `PAGE_MMUSHIFT`, TCG-only.
- RIP→symbol: `scratchpad/rip2sym.py` (System.map; `CONFIG_DEBUG_INFO_NONE`, so
  no line numbers — function-level only).

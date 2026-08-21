default Order dec

$include <prelude.sail>

// ============================================================
// Tessera hardware-state model: machine skeleton + RISC-V Sv39
// translation walk + per-core TLB + SFENCE.VMA.
// Written functionally (Sail is first-order, so memory is an
// explicit association list) so the Coq backend emits clean
// definitions for the Iris track (property2/coq).
// ============================================================

// Addresses (RISC-V Sv39: 64-bit VA, 56-bit PA, 44-bit PPN).
type vaddr = bits(64)
type paddr = bits(56)

// Mapping permissions -- the Tessera-relevant subset (read / write).
enum Perm = { None_, Read, ReadWrite }

// RISC-V Sv39 page-table entry (leaf view): V, R, W, X, U, the Svnapot N bit
// (PTE[63]), + PPN.
struct Pte = {
  valid : bool,
  read  : bool,
  write : bool,
  exec  : bool,
  user  : bool,
  napot : bool,
  ppn   : bits(44)
}

// A TLB entry: the full virtual address it was filled from, its VPN, the
// physical page number, and perms.  RISC-V matches on `vpn` only, but VIVT/VIPT
// variants index/tag by the full `vaddr` (the low-order set-index bits live in
// the page offset, which `vpn` discards) — so each entry ("cell") is coupled to
// the virtual address that produced it.
struct TlbEntry = {
  vaddr : vaddr,      // full VA the entry was filled for (VIVT/VIPT index/tag)
  vpn   : bits(27),   // Sv39 VPN = VA[38..12]
  ppn   : bits(44),   // the (raw) leaf PPN; for a NAPOT entry find_tlb uses ppn[43..4]
  perm  : Perm,
  napot : bool        // 64KiB NAPOT page (tags VA[38..16]) vs 4KiB (tags VA[38..12])
}

// One core: the root page-table PPN (satp.PPN), its private TLB, and its
// topology placement — the hardware-thread id (hart, an SMT thread within a
// core) and the NUMA node the core belongs to (SSG-1).  The shootdown
// correctness so far is topology-agnostic; these fields are the plumbing that
// future topology-sensitive properties (SMT co-residency, NUMA locality) attach
// to.
struct Core = {
  satp_ppn : bits(44),
  tlb      : list(TlbEntry),
  hart     : int,
  node     : int
}

// Physical memory, as a sparse association list: (PTE physical address, PTE).
// The walk reads PTEs by address; a missing address means the walk faults.
struct MemEntry = {
  addr : paddr,
  pte  : Pte
}

type PageTable = list(MemEntry)

// Data RAM: byte-addressable physical memory, as a sparse association list of
// bytes (the data-side twin of PageTable).  This closes the G3 gap — the machine
// now has real data storage, so data load/store correctness is in scope.
// A missing address means an unmapped/faulting access.
struct Byte = {
  addr : paddr,
  data : bits(8)
}

type Ram = list(Byte)

// An IOMMU translation-cache (IOTLB) entry (SSG-4): the device identity
// (StreamID / BDF), its PASID (0 = no SVM), the device virtual address (IOVA)
// the translation was filled for, the translated physical address, and perms
// (devices never execute).  This is the ATS translation-completion content the
// IOMMU caches — the device-side twin of TlbEntry.
struct IotlbEntry = {
  did   : int,
  pasid : int,
  iova  : vaddr,
  pa    : paddr,
  perm  : Perm
}

// An endpoint device's own translation cache (device-TLB), filled by an ATS
// translation completion and invalidated by an ATS invalidation.  Keyed by
// (did, iova) — the device-side twin of the core TLB, one per device rather
// than per core (did is the StreamID/BDF; PASID is 0 for no SVM and lives in
// the mirrored IOTLB entry).
struct DevTlbEntry = {
  did  : int,
  iova : vaddr,
  pa   : paddr,
  perm : Perm
}

// A PRI page request: on a translation fault the device asks the kernel to map
// the page and retries.  Pending until the kernel maps + the device retries.
struct PriRequest = {
  did  : int,
  iova : vaddr
}

// A queued-invalidation descriptor (VT-d IOTLB Invalidate / Invalidation-Wait,
// SMMU CMDQ, AMD-Vi command buffer).  is_wait = true is Invalidation-Wait (the
// completion barrier); is_wait = false is IotlbInvalidate va (a 4KiB selective
// IOTLB invalidation).  The circular-buffer head/tail MMIO is the weak-memory
// lift's job (S4.2b-2); here the queue is a plain FIFO list.
struct InvalidationCmd = {
  is_wait : bool,
  va      : vaddr
}

// SMMUv3 stream table / context descriptor (SSG-4 / S4.4): the structural layer
// over `smmu_walk`.  The Stream ID (SID) indexes the stream table (list
// position = SID, SMMUv3 §3.3.1); the Stream Table Entry (STE) carries the
// stage-2 table root and a pointer into the context-descriptor table; the
// Context Descriptor (CD) carries the stage-1 table root (and ASID for later
// address-space tagging).  Declared before `Machine` because the machine state
// carries both tables.
struct Ste = {
  valid   : bool,
  s2_root : bits(44),
  cd_ptr  : int
}

struct Cd = {
  valid   : bool,
  s1_root : bits(44),
  asid    : int
}

// Intel VT-d context entry (VT-d §3.3 / §6.2): the requester-ID-indexed
// context table selects a domain and its second-level paging root.  This first
// slice deliberately models only the present bit, domain ID, and second-level
// root; fault-recording, PASID tables, and scalable-mode device tables remain
// later SSG-4 increments.
struct VtdContext = {
  present : bool,
  did     : int,
  sl_root : bits(44)
}

// The machine: a set of cores sharing one physical memory (page-table
// descriptors plus data RAM), a per-core IPI mailbox (SSG-3 / S2.3), the
// IOMMU's translation cache (SSG-4) — the device-side twin of the per-core
// TLBs — and the SMMUv3 stream table + context-descriptor table (S4.4).
struct Machine = {
  cores   : list(Core),
  mem     : PageTable,
  ram     : Ram,
  ipi     : list(bool),
  iotlb   : list(IotlbEntry),
  devtlbs : list(DevTlbEntry),
  prireqs : list(PriRequest),
  ioqueue : list(InvalidationCmd),
  stes    : list(Ste),
  cds     : list(Cd)
}

// ---- VPN / offset extraction (Sv39) ----

// vpn3 is the extra top level of the AMD-Vi 4-level walk (bits [47..39]);
// unused by the 3-level Sv39 walk but present for S4.4's AMD-Vi walker.
val vpn3 : vaddr -> bits(9)
function vpn3(va) = va[47 .. 39]

val vpn2 : vaddr -> bits(9)
function vpn2(va) = va[38 .. 30]

val vpn1 : vaddr -> bits(9)
function vpn1(va) = va[29 .. 21]

val vpn0 : vaddr -> bits(9)
function vpn0(va) = va[20 .. 12]

val vpn_of : vaddr -> bits(27)
function vpn_of(va) = va[38 .. 12]

val page_offset : vaddr -> bits(12)
function page_offset(va) = va[11 .. 0]

// ---- address arithmetic ----

val pte_address : (bits(44), bits(9)) -> paddr
function pte_address(table_ppn, index) =
  sail_shiftleft(sail_zero_extend(table_ppn, 56), 12) | sail_shiftleft(sail_zero_extend(index, 56), 3)

val phys_addr : (bits(44), bits(12)) -> paddr
function phys_addr(ppn, off) =
  sail_shiftleft(sail_zero_extend(ppn, 56), 12) | sail_zero_extend(off, 56)

// ---- Svnapot (extension N bit, PTE[63]) ----
//
// A leaf PTE with the N bit set is a naturally aligned power-of-two (NAPOT)
// page.  Only the 64KiB encoding is valid: the low 4 PPN bits must be 0b1000
// (the "contiguity" pattern), and the physical page is ppn[43..4] followed by
// the 16-bit page offset VA[15..0].  This transcribes sail-riscv
// model/sys/vmem.sail (pt_walk, the Svnapot clause) and vmem_pte.sail (the
// PTE_Ext.N bitfield).

val napot_guard : bits(44) -> bool
function napot_guard(ppn) = ppn[3 .. 0] == 0b1000

val napot_phys_addr : (bits(44), vaddr) -> paddr
function napot_phys_addr(ppn, va) =
  sail_shiftleft(sail_zero_extend(ppn[43 .. 4], 56), 16) | sail_zero_extend(va[15 .. 0], 56)

// ---- PTE interpretation ----

val is_leaf : Pte -> bool
function is_leaf(pte) =
  if pte.read then true
  else if pte.write then true
  else if pte.exec then true
  else false

val perm_of_pte : Pte -> Perm
function perm_of_pte(pte) =
  if pte.write then ReadWrite
  else if pte.read then Read
  else None_

// ---- memory read ----

val read_pte : (PageTable, paddr) -> option(Pte)
function read_pte(mem, addr) = match mem {
  [||] => None(),
  e :: rest =>
    if e.addr == addr then Some(e.pte)
    else read_pte(rest, addr)
}

// ---- data RAM read / write (byte-addressable) ----

val read_byte : (Ram, paddr) -> option(bits(8))
function read_byte(ram, addr) = match ram {
  [||] => None(),
  b :: rest =>
    if b.addr == addr then Some(b.data)
    else read_byte(rest, addr)
}

val write_byte : (Ram, paddr, bits(8)) -> Ram
function write_byte(ram, addr, v) = match ram {
  [||] => struct { addr = addr, data = v } :: [||],
  b :: rest =>
    if b.addr == addr then struct { addr = addr, data = v } :: rest
    else b :: write_byte(rest, addr, v)
}

// ---- address decode (the "decode" half of the G3 gap) ----
//
// A physical address is decoded to the region that serves it before any data
// access (the data-side twin of the MMU walk's PTE interpretation).  RAM is
// served by `read_byte`/`write_byte`; MMIO is served by a device, which the
// model does not yet have (SSG-5..8), so a device access faults.  Illustrative
// one-bit split — PA[55] = 0 is RAM (the low 2^55 bytes), PA[55] = 1 is the
// device window.  The real per-platform map (QEMU virt PLIC/UART windows etc.)
// replaces this constant once devices land; what the proofs rely on is only
// that the decode step exists and is respected by loads/stores.

enum Region = { RAM, MMIO }

val decode_addr : paddr -> Region
function decode_addr(pa) =
  if pa[55] == 0b0 then RAM else MMIO

// ---- hardware page-table walk (3 levels, Sv39) ----

val translate : (Core, PageTable, vaddr) -> option((paddr, Perm))
function translate(core, mem, va) = {
  let l2 : option(Pte) = read_pte(mem, pte_address(core.satp_ppn, vpn2(va)));
  match l2 {
    None() => None(),
    Some(p2) =>
      if p2.valid then {
        if is_leaf(p2) then None()
        // Svnapot: N=1 on a non-leaf PTE is reserved (upstream pte_is_invalid's
        // "non-leaf & ext bits != 0" clause) and faults.
        else if p2.napot then None()
        else {
          let l1 : option(Pte) = read_pte(mem, pte_address(p2.ppn, vpn1(va)));
          match l1 {
            None() => None(),
            Some(p1) =>
              if p1.valid then {
                if is_leaf(p1) then None()
                else if p1.napot then None()
                else {
                  let l0 : option(Pte) = read_pte(mem, pte_address(p1.ppn, vpn0(va)));
                  match l0 {
                    None() => None(),
                    Some(p0) =>
                      if p0.valid then {
                        // Reserved Sv39 encoding R=0, W=1 (an SS page when X=0, or
                        // otherwise-reserved when X=1) must fault, not translate.
                        if p0.write & not_bool(p0.read) then None()
                        else if is_leaf(p0) then {
                          // Svnapot: N=1 is a 64KiB NAPOT page (ppn[3..0] must be
                          // 0b1000, else reserved -> fault); N=0 is a normal 4KiB
                          // page.
                          if p0.napot then {
                            if napot_guard(p0.ppn) then Some((napot_phys_addr(p0.ppn, va), perm_of_pte(p0)))
                            else None()
                          } else Some((phys_addr(p0.ppn, page_offset(va)), perm_of_pte(p0)))
                        }
                        else None()
                      } else None()
                  }
                }
              } else None()
          }
        }
      } else None()
  }
}

// ---- IOMMU translation (SSG-4) ----
//
// The IOMMU's walk is the *same* Sv39 walk as `translate`, but rooted at the
// domain's page-table root (the IOMMU is not a core) and over the device's IOVA.
// First-level-only (one shared GPA->SPA table with the CPU); PASID/SVM
// second-level (GVA->GPA) is a later increment.
val iommu_walk : (bits(44), PageTable, vaddr) -> option((paddr, Perm))
function iommu_walk(root, mem, iova) =
  translate(struct { satp_ppn = root, tlb = [||], hart = 0, node = 0 }, mem, iova)

// ---- SMMUv3 two-stage translation (SSG-4 / S4.4) ----
//
// The SMMU's distinctive feature over the CPU MMU: a *two-stage* walk.  Stage-1
// (GVA -> GPA) is re-rooted at the context descriptor's stage-1 table; stage-2
// (GPA -> SPA) is re-rooted at the stream table's stage-2 table.  Both stages
// reuse the same Sv39 walk; the stage-1 GPA is zero-extended to a VA for the
// stage-2 input (SMMUv3 §3.3, the stage-1/stage-2 composition).
val smmu_walk : (bits(44), bits(44), PageTable, vaddr) -> option((paddr, Perm))
function smmu_walk(s1_root, s2_root, mem, gva) =
  match translate(struct { satp_ppn = s1_root, tlb = [||], hart = 0, node = 0 }, mem, gva) {
    None() => None(),
    Some((gpa, _)) =>
      translate(struct { satp_ppn = s2_root, tlb = [||], hart = 0, node = 0 }, mem,
               sail_zero_extend(gpa, 64))
  }

// ---- AMD-Vi 4-level I/O page-table walk (SSG-4 / S4.4) ----
//
// AMD-Vi's distinctive feature: a *4-level* I/O page table (52-bit GPA,
// 4 x 9-bit levels + 12-bit offset) vs Sv39's 3 levels.  Modelled as the extra
// top level (vpn3) resolving to a non-leaf PTE, then the bottom 3 levels are
// exactly the Sv39 `translate` re-rooted at that PTE.
val amdvi_walk : (bits(44), PageTable, vaddr) -> option((paddr, Perm))
function amdvi_walk(root, mem, iova) =
  match read_pte(mem, pte_address(root, vpn3(iova))) {
    None() => None(),
    Some(p3) =>
      if p3.valid & not_bool(is_leaf(p3)) & not_bool(p3.napot) then
        translate(struct { satp_ppn = p3.ppn, tlb = [||], hart = 0, node = 0 }, mem, iova)
      else None()
  }

// ---- SMMUv3 stream table / context descriptor (SSG-4 / S4.4) ----
//
// The two-stage walk's roots are resolved by the stream-table walk: the Stream
// ID (SID) indexes the stream table (list position = SID, SMMUv3 §3.3.1); the
// Stream Table Entry (STE) carries the stage-2 table root and a pointer into
// the context-descriptor table; the Context Descriptor (CD) carries the stage-1
// table root (and ASID for later address-space tagging).  This is the
// structural layer over `smmu_walk` (S4.4): STE + CD select the two roots.
// (The Ste/Cd structs are declared above, before `Machine`, because Machine
// carries the stream table and context-descriptor table as state.)

// list_nth-style lookup: element at position i, None out of range.
val ste_lookup : (list(Ste), int) -> option(Ste)
function ste_lookup(stes, sid) = match (stes, sid) {
  (s :: _, 0) => Some(s),
  (_ :: rest, n) => ste_lookup(rest, n - 1),
  ([||], _) => None()
}

val cd_lookup : (list(Cd), int) -> option(Cd)
function cd_lookup(cds, idx) = match (cds, idx) {
  (c :: _, 0) => Some(c),
  (_ :: rest, n) => cd_lookup(rest, n - 1),
  ([||], _) => None()
}

// The full SMMU translate: SID -> STE -> CD -> two-stage walk.  An invalid STE,
// a missing/invalid CD, or a faulting stage faults; a hit returns exactly
// `smmu_walk(c.s1_root, s.s2_root, mem, gva)` (the conformance lemma S4.4).
val smmu_translate : (list(Ste), list(Cd), int, PageTable, vaddr) -> option((paddr, Perm))
function smmu_translate(stes, cds, sid, mem, gva) =
  match ste_lookup(stes, sid) {
    None() => None(),
    Some(s) =>
      if s.valid then
        match cd_lookup(cds, s.cd_ptr) {
          None() => None(),
          Some(c) =>
            if c.valid then smmu_walk(c.s1_root, s.s2_root, mem, gva)
            else None()
        }
      else None()
  }

// ---- Intel VT-d context-table / second-level walk (SSG-4 / S4.5) ----
//
// Legacy VT-d indexes a context entry by PCIe Requester ID.  A present context
// selects a domain ID and a second-level root; the second-level walk is the
// same four-level-capable IOMMU interface represented here by `iommu_walk`.
// PASID first-stage translation and scalable-mode device/ PASID tables are
// intentionally separate follow-on increments.
val vtd_context_lookup : (list(VtdContext), int) -> option(VtdContext)
function vtd_context_lookup(contexts, rid) = match (contexts, rid) {
  (c :: _, 0) => Some(c),
  (_ :: rest, n) => vtd_context_lookup(rest, n - 1),
  ([||], _) => None()
}

val vtd_walk : (list(VtdContext), int, PageTable, vaddr) -> option((paddr, Perm))
function vtd_walk(contexts, rid, mem, iova) =
  match vtd_context_lookup(contexts, rid) {
    None() => None(),
    Some(c) =>
      if c.present then iommu_walk(c.sl_root, mem, iova)
      else None()
  }

// ---- Intel VT-d first-stage / PASID translation (SSG-4 / S4.5) ----
//
// VT-d scalable mode's distinctive feature over the CPU MMU (and over the S4.5
// second-level slice) is a two-stage walk.  The guest (first) stage GVA -> GPA
// is re-rooted at a first-stage table selected by a PASID-indexed PASID table
// (VT-d 5.20 §15.2, the PASID-table lookup), and the host (second) stage
// GPA -> SPA is the context's second-level walk.  Both stages reuse the Sv39
// walk; the first-stage GPA is zero-extended to a VA for the second-stage
// input (VT-d 5.20 §15.6, first-stage/second-stage composition).  A PASID table
// entry is minimal here (present + first-stage root); scalable-mode device
// tables, PASID-cache lookup, and per-PASID coherency are later increments.
struct VtdPasid = {
  present : bool,
  s1_root : bits(44)
}

val vtd_pasid_lookup : (list(VtdPasid), int) -> option(VtdPasid)
function vtd_pasid_lookup(ptes, pasid) = match (ptes, pasid) {
  (e :: _, 0) => Some(e),
  (_ :: rest, n) => vtd_pasid_lookup(rest, n - 1),
  ([||], _) => None()
}

val vtd_walk_pasid : (list(VtdContext), int, list(VtdPasid), int, PageTable, vaddr) -> option((paddr, Perm))
function vtd_walk_pasid(contexts, rid, ptes, pasid, mem, iova) =
  match vtd_context_lookup(contexts, rid) {
    None() => None(),
    Some(c) =>
      if c.present then
        match vtd_pasid_lookup(ptes, pasid) {
          None() => None(),
          Some(e) =>
            if e.present then
              match iommu_walk(e.s1_root, mem, iova) {
                None() => None(),
                Some((gpa, _)) =>
                  iommu_walk(c.sl_root, mem, sail_zero_extend(gpa, 64))
              }
            else None()
        }
      else None()
  }

// ---- Intel VT-d PASID cache (SSG-4 / S4.5) ----
//
// VT-d scalable mode caches the PASID-table / first-stage lookup (the PASID
// cache, VT-d 5.20 §15.4) so an access need not re-walk the guest tables.  A
// cache entry is minimal here: present + the resolved first-stage root.
// `pasid_cached_walk` is the two-stage walk with the cache standing in for the
// PASID table; the coherence invariant (`pasid_cache ⊆ pasid-table`) says a
// present cached root matches the table, so `pasid_cached_walk =
// vtd_walk_pasid` (proved in vtd_proofs.v).  Cache eviction on invalidation
// and the PASID-cache tag (DID+PASID) are later increments.
struct PasidCacheEntry = {
  present : bool,
  pasid   : int,
  s1_root : bits(44)
}

val pasid_cache_lookup : (list(PasidCacheEntry), int) -> option(PasidCacheEntry)
function pasid_cache_lookup(cache, pasid) = match (cache, pasid) {
  (e :: _, 0) => Some(e),
  (_ :: rest, n) => pasid_cache_lookup(rest, n - 1),
  ([||], _) => None()
}

val pasid_cached_walk : (list(VtdContext), int, list(PasidCacheEntry), int, PageTable, vaddr) -> option((paddr, Perm))
function pasid_cached_walk(contexts, rid, cache, pasid, mem, iova) =
  match vtd_context_lookup(contexts, rid) {
    None() => None(),
    Some(c) =>
      if c.present then
        match pasid_cache_lookup(cache, pasid) {
          None() => None(),
          Some(e) =>
            if e.present then
              match iommu_walk(e.s1_root, mem, iova) {
                None() => None(),
                Some((gpa, _)) =>
                  iommu_walk(c.sl_root, mem, sail_zero_extend(gpa, 64))
              }
            else None()
        }
      else None()
  }

// ---- Intel VT-d scalable-mode device table (SSG-4 / S4.5) ----
//
// VT-d scalable mode indexes the *device table* by requester ID (BDF); each
// device-table entry (DTE) selects a context table (and, with SVM, the PASID
// table) rather than the legacy flat context table (VT-d 5.20 §3.4).  Here a
// DTE selects a context by index into the shared contexts list, so the
// device-table walk is the context's second-level walk re-rooted at the
// selected entry: `vtd_walk_device` reduces to `vtd_walk` exactly when the
// selected context is the one the flat lookup would find (proved in
// vtd_proofs.v).  PASID-table pointers in the DTE (scalable-mode SVM) remain
// a later increment.
struct VtdDeviceEntry = {
  present   : bool,
  did       : int,
  ctx_index : int
}

val vtd_device_lookup : (list(VtdDeviceEntry), int) -> option(VtdDeviceEntry)
function vtd_device_lookup(devtbl, rid) = match (devtbl, rid) {
  (e :: _, 0) => Some(e),
  (_ :: rest, n) => vtd_device_lookup(rest, n - 1),
  ([||], _) => None()
}

val vtd_walk_device : (list(VtdDeviceEntry), list(VtdContext), int, PageTable, vaddr) -> option((paddr, Perm))
function vtd_walk_device(devtbl, contexts, rid, mem, iova) =
  match vtd_device_lookup(devtbl, rid) {
    None() => None(),
    Some(d) =>
      if d.present then
        match vtd_context_lookup(contexts, d.ctx_index) {
          None() => None(),
          Some(c) => if c.present then iommu_walk(c.sl_root, mem, iova) else None()
        }
      else None()
  }

// ---- PASID-cache eviction / refill (SSG-4 / S4.5) ----
//
// The PASID cache (VT-d 5.20 §15.4) is indexed by PASID: invalidation clears
// the cached first-stage root for a PASID — the entry turns non-present, so
// the cached two-stage walk misses and the IOMMU must re-walk the PASID
// table; refill re-installs the table's root.  Together with
// `pasid_cache_coherent` (the cache ⊆ table invariant), eviction is what
// *breaks* coherence and refill what *restores* it: the miss/refill cycle a
// translation after invalidation must go through.
val pasid_cache_evict : (list(PasidCacheEntry), int) -> list(PasidCacheEntry)
function pasid_cache_evict(cache, pasid) = match (cache, pasid) {
  (e :: rest, 0) => struct { present = false, pasid = e.pasid, s1_root = e.s1_root } :: rest,
  (e :: rest, n) => e :: pasid_cache_evict(rest, n - 1),
  ([||], _) => [||]
}

val pasid_cache_refill : (list(PasidCacheEntry), int, bits(44)) -> list(PasidCacheEntry)
function pasid_cache_refill(cache, pasid, root) = match (cache, pasid) {
  (e :: rest, 0) => struct { present = true, pasid = 0, s1_root = root } :: rest,
  (e :: rest, n) => e :: pasid_cache_refill(rest, n - 1, root),
  ([||], _) => [||]
}

// ---- Intel VT-d fault recording (SSG-4 / S4.5) ----
//
// On a translation fault VT-d records (requester ID, PASID, IOVA, reason) in
// its fault log and signals an interrupt (VT-d 5.20 §6.1, fault recording).
// The reason is an enum naming exactly which structural or page-table step
// faulted; `vtd_record_fault` mirrors the two-stage walk one-to-one, returning
// [|sed] on the same paths the walk faults on and [||] on a hit — so a fault
// is recorded iff the walk faults.  FRCD-cache storage, fault-message
// (DID/PASID) signalling, and ATS/PRQ fault handling are later increments.
enum FaultReason = {
  FR_ContextMissing,
  FR_ContextNotPresent,
  FR_PasidMissing,
  FR_PasidNotPresent,
  FR_Stage1Fault,
  FR_Stage2Fault
}

struct FaultRecord = {
  did    : int,
  pasid  : int,
  iova   : vaddr,
  reason : FaultReason
}

val vtd_record_fault : (list(VtdContext), int, list(VtdPasid), int, PageTable, vaddr) -> option(FaultRecord)
function vtd_record_fault(contexts, rid, ptes, pasid, mem, iova) =
  match vtd_context_lookup(contexts, rid) {
    None() => Some(struct { did = rid, pasid = pasid, iova = iova, reason = FR_ContextMissing }),
    Some(c) =>
      if c.present then
        match vtd_pasid_lookup(ptes, pasid) {
          None() => Some(struct { did = rid, pasid = pasid, iova = iova, reason = FR_PasidMissing }),
          Some(e) =>
            if e.present then
              match iommu_walk(e.s1_root, mem, iova) {
                None() => Some(struct { did = rid, pasid = pasid, iova = iova, reason = FR_Stage1Fault }),
                Some((gpa, _)) =>
                  match iommu_walk(c.sl_root, mem, sail_zero_extend(gpa, 64)) {
                    None() => Some(struct { did = rid, pasid = pasid, iova = iova, reason = FR_Stage2Fault }),
                    Some(_) => None()
                  }
              }
            else Some(struct { did = rid, pasid = pasid, iova = iova, reason = FR_PasidNotPresent })
        }
      else Some(struct { did = rid, pasid = pasid, iova = iova, reason = FR_ContextNotPresent })
  }

// ---- Intel VT-d fault-record cache (FRCD) + fault-message signalling (SSG-4 / S4.5) ----
//
// On a translation fault the IOMMU records a Fault Record Cache Descriptor
// (FRCD: DID, PASID, IOVA, reason) and raises the fault interrupt; software
// drains FRCD entries to learn which endpoint / address faulted (VT-d 5.20
// §6.1).  `frcd_record` prepends the record, `frcd_lookup` scans by
// (did, pasid, iova), `frcd_pending` is the interrupt line (pending iff the
// FRCD holds a fault), and `fault_msg_did_pasid` is the interrupt payload —
// the DID+PASID identifying the faulting endpoint.  A record is produced iff
// a fault was taken (`vtd_record_fault`), so a pending FRCD entry ⟺ an
// outstanding fault (proved in vtd_proofs.v).  FRCDR drain-by-software and
// ATS/PRQ fault handling remain later increments.
struct FrcdEntry = {
  did    : int,
  pasid  : int,
  iova   : vaddr,
  reason : FaultReason
}

val frcd_record : (FaultRecord, list(FrcdEntry)) -> list(FrcdEntry)
function frcd_record(fr, cache) =
  struct { did = fr.did, pasid = fr.pasid, iova = fr.iova, reason = fr.reason } :: cache

val frcd_matches : (FrcdEntry, int, int, vaddr) -> bool
function frcd_matches(e, d, p, va) = e.did == d & e.pasid == p & e.iova == va

val frcd_lookup : (list(FrcdEntry), (int, int), vaddr) -> option(FrcdEntry)
function frcd_lookup(cache, dp, va) = match cache {
  [||] => None(),
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p & e.iova == va then Some(e)
    else frcd_lookup(rest, dp, va)
}

val frcd_pending : list(FrcdEntry) -> bool
function frcd_pending(cache) = match cache {
  [||] => false,
  _    => true
}

val fault_msg_did_pasid : FrcdEntry -> (int, int)
function fault_msg_did_pasid(e) = (e.did, e.pasid)

// The IOMMU shootdown's invalidate (SSG-4): drop every cached translation whose
// IOVA is the page being unmapped.  VT-d IOTLB Invalidate (6.5.2.3) / SMMU TLBI
// (4.4) / AMD-Vi INVALIDATE_IOMMU_PAGES (2.4.3).  4KiB granularity for now;
// NAPOT large-page invalidation mirrors tag_eq as a later increment.
val iotlb_invalidate : (list(IotlbEntry), vaddr) -> list(IotlbEntry)
function iotlb_invalidate(entries, va) = match entries {
  [||] => [||],
  e :: rest =>
    if vpn_of(e.iova) == vpn_of(va) then iotlb_invalidate(rest, va)
    else e :: iotlb_invalidate(rest, va)
}

// ---- queued invalidation (SSG-4 / S4.2b) ----

// The IOMMU's command-queue drain: process the FIFO in order, applying each
// IotlbInvalidate to the IOTLB, and complete (Some iotlb) when an
// Invalidation-Wait is reached — the Invalidation-Wait completion (VT-d
// §6.5.2.9) that orders the prior invalidations.  A queue with no wait
// descriptor drains to None (no completion).
val iommu_process_queue : (list(InvalidationCmd), list(IotlbEntry)) -> option(list(IotlbEntry))
function iommu_process_queue(queue, iotlb) = match queue {
  [||] => None(),
  c :: rest =>
    if c.is_wait then Some(iotlb)
    else iommu_process_queue(rest, iotlb_invalidate(iotlb, c.va))
}

// ---- ATS / PRI device side (SSG-4 / S4.3) ----

// ATS translation request -> completion.  The IOMMU walks the shared page table;
// on a hit it caches the completion into its IOTLB and fills the device's
// device-TLB with it.  On a fault nothing is cached (the device issues a PRI
// page request instead).
val ats_translate : (list(IotlbEntry), list(DevTlbEntry), bits(44), int, vaddr, PageTable)
                 -> (list(IotlbEntry), list(DevTlbEntry))
function ats_translate(iotlb, devtlbs, root, did, iova, mem) =
  match iommu_walk(root, mem, iova) {
    None() => (iotlb, devtlbs),
    Some((pa, perm)) =>
      (struct { did = did, pasid = 0, iova = iova, pa = pa, perm = perm } :: iotlb,
       struct { did = did, iova = iova, pa = pa, perm = perm } :: devtlbs)
  }

// ATS device-TLB invalidation: drop every endpoint device-TLB entry for the
// unmapped page (the per-device tier; the IOMMU's own IOTLB is invalidated by
// iotlb_invalidate).  PCIe ATS (4.3) / SMMU (4.5) / AMD-Vi (2.11).
val ats_invalidate : (list(DevTlbEntry), vaddr) -> list(DevTlbEntry)
function ats_invalidate(devtlbs, va) = match devtlbs {
  [||] => [||],
  e :: rest =>
    if vpn_of(e.iova) == vpn_of(va) then ats_invalidate(rest, va)
    else e :: ats_invalidate(rest, va)
}

// ---- ALL-granularity invalidation (SSG-4) ----

// The ALL invalidation (AMD-Vi INVALIDATE_IOMMU_ALL §2.4.8 / SMMU TLBI_ALL
// §4.4): drop every cached IOTLB translation, regardless of IOVA.  The second
// invalidation shape beside the 4KiB selective `iotlb_invalidate`.
val iotlb_invalidate_all : list(IotlbEntry) -> list(IotlbEntry)
function iotlb_invalidate_all(entries) = [||]

// The device-side ALL invalidation: drop every endpoint device-TLB entry.
val ats_invalidate_all : list(DevTlbEntry) -> list(DevTlbEntry)
function ats_invalidate_all(devtlbs) = [||]

// ---- ASID / domain-granularity invalidation (SSG-4 / S4.4) ----
//
// The coarser invalidation shapes beside the 4KiB selective `iotlb_invalidate`
// and the ALL `iotlb_invalidate_all`: drop every cached translation matching a
// tag — SMMU TLBI-by-ASID (the pasid tag, §4.4) and AMD-Vi
// INVALIDATE_IOMMU_PAGES-by-domain (the did tag, §2.4.3).
val iotlb_invalidate_pasid : (list(IotlbEntry), int) -> list(IotlbEntry)
function iotlb_invalidate_pasid(entries, asid) = match entries {
  [||] => [||],
  e :: rest =>
    if e.pasid == asid then iotlb_invalidate_pasid(rest, asid)
    else e :: iotlb_invalidate_pasid(rest, asid)
}

val iotlb_invalidate_domain : (list(IotlbEntry), int) -> list(IotlbEntry)
function iotlb_invalidate_domain(entries, did) = match entries {
  [||] => [||],
  e :: rest =>
    if e.did == did then iotlb_invalidate_domain(rest, did)
    else e :: iotlb_invalidate_domain(rest, did)
}

// PRI page request: enqueue a request to map the page (at most one pending per
// (did, iova) — a device retries the same fault, it does not issue fresh ones).
val pri_request : (list(PriRequest), int, vaddr) -> list(PriRequest)
function pri_request(prireqs, did, iova) = match prireqs {
  [||] => struct { did = did, iova = iova } :: [||],
  r :: rest =>
    if r.did == did & r.iova == iova then prireqs
    else r :: pri_request(rest, did, iova)
}

// ---- TLB lookup / invalidation ----

// TLB tag match: a 64KiB NAPOT entry tags on VA[38..16] (the high 23 VPN bits —
// the low 4 VPN bits are subsumed by the page), a 4KiB entry on the full VPN.
val tag_eq : (TlbEntry, bits(27)) -> bool
function tag_eq(e, vpn) =
  if e.napot then e.vpn[26 .. 4] == vpn[26 .. 4]
  else e.vpn == vpn

// The physical address a TLB entry translates va to: a 4KiB entry is
// ppn @ VA[11..0]; a 64KiB NAPOT entry is ppn[43..4] @ VA[15..0] (napot_phys_addr
// ignores the low 4 PPN bits, the 0b1000 contiguity pattern).
val tlb_pa : (TlbEntry, vaddr) -> paddr
function tlb_pa(e, va) =
  if e.napot then napot_phys_addr(e.ppn, va)
  else phys_addr(e.ppn, page_offset(va))

// TLB lookup: find the first entry whose tag matches, and compose its PA.
val find_tlb : (list(TlbEntry), vaddr) -> option((paddr, Perm))
function find_tlb(entries, va) = match entries {
  [||] => None(),
  e :: rest =>
    if tag_eq(e, vpn_of(va)) then Some((tlb_pa(e, va), e.perm))
    else find_tlb(rest, va)
}

val tlb_lookup : (Core, vaddr) -> option((paddr, Perm))
function tlb_lookup(core, va) = find_tlb(core.tlb, va)

// The endpoint's device-TLB lookup: the device consults its cached translation
// for iova (the device-side twin of find_tlb; 4KiB granularity, no NAPOT).
val find_devtlb : (list(DevTlbEntry), vaddr) -> option((paddr, Perm))
function find_devtlb(entries, iova) = match entries {
  [||] => None(),
  e :: rest =>
    if vpn_of(e.iova) == vpn_of(iova) then Some((e.pa, e.perm))
    else find_devtlb(rest, iova)
}

// SFENCE.VMA all: invalidate every TLB entry on this core.
val sfence_vma_all : Core -> Core
function sfence_vma_all(core) = struct {
  satp_ppn = core.satp_ppn,
  tlb      = [||],
  hart     = core.hart,
  node     = core.node
}

// SFENCE.VMA by VA: drop only entries matching the virtual page.
val filter_tlb : (list(TlbEntry), bits(27)) -> list(TlbEntry)
function filter_tlb(entries, vpn) = match entries {
  [||] => [||],
  e :: rest =>
    if tag_eq(e, vpn) then filter_tlb(rest, vpn)
    else e :: filter_tlb(rest, vpn)
}

val sfence_vma_va : (Core, vaddr) -> Core
function sfence_vma_va(core, va) = struct {
  satp_ppn = core.satp_ppn,
  tlb      = filter_tlb(core.tlb, vpn_of(va)),
  hart     = core.hart,
  node     = core.node
}

// ---- IPI delivery (SSG-3 / S2.3) ----
//
// The shootdown so far is a functional broadcast (map sfence_vma_va over the
// cores); there is no IPI-delivery transition.  SSG-3 adds one: the leader marks
// core i's shootdown IPI delivered (deliver_ipi), and the remote only clears its
// TLB once the IPI has been delivered (receive_ipi).  The delivered bits live in
// Machine.ipi, parallel to Machine.cores.  receive_ipi's guard is the pure-model
// form of "delivery precedes ack": a remote cannot flush (ack) before delivery.

// Update list element i (recursive; out-of-range index leaves the list alone).
val list_update_bool : (list(bool), int, bool) -> list(bool)
function list_update_bool(l, i, v) = match (l, i) {
  (_ :: rest, 0) => v :: rest,
  (x :: rest, n) => x :: list_update_bool(rest, n - 1, v),
  ([||], _) => [||]
}

// Read list element i, with a default for out-of-range.
val list_nth_bool : (list(bool), int, bool) -> bool
function list_nth_bool(l, i, d) = match (l, i) {
  (x :: _, 0) => x,
  (_ :: rest, n) => list_nth_bool(rest, n - 1, d),
  ([||], _) => d
}

// deliver_ipi: the leader marks core i's shootdown IPI delivered.
val deliver_ipi : (Machine, int) -> Machine
function deliver_ipi(m, i) = struct {
  cores   = m.cores,
  mem     = m.mem,
  ram     = m.ram,
  ipi     = list_update_bool(m.ipi, i, true),
  iotlb   = m.iotlb,
  devtlbs = m.devtlbs,
  prireqs = m.prireqs,
  ioqueue = m.ioqueue,
  stes    = m.stes,
  cds     = m.cds
}

// Walk the cores, flushing `va` from core i's TLB iff `delivered` holds (the
// delivered bit is read once by receive_ipi and carried down as a parameter).
// (The VA being flushed is the shootdown's VA; the IPI delivers the signal, the
// VA is communicated out-of-band.)
val receive_ipi_cores : (list(Core), int, bool, vaddr) -> list(Core)
function receive_ipi_cores(cores, i, delivered, va) = match (cores, i) {
  (c :: cs, 0) => (if delivered then sfence_vma_va(c, va) else c) :: cs,
  (c :: cs, n) => c :: receive_ipi_cores(cs, n - 1, delivered, va),
  ([||], _) => [||]
}

// receive_ipi: core i takes its IPI and flushes `va` from its TLB — but only if
// the IPI was delivered first (ipi[i] = true).
val receive_ipi : (Machine, int, vaddr) -> Machine
function receive_ipi(m, i, va) = struct {
  cores   = receive_ipi_cores(m.cores, i, list_nth_bool(m.ipi, i, false), va),
  mem     = m.mem,
  ram     = m.ram,
  ipi     = m.ipi,
  iotlb   = m.iotlb,
  devtlbs = m.devtlbs,
  prireqs = m.prireqs,
  ioqueue = m.ioqueue,
  stes    = m.stes,
  cds     = m.cds
}

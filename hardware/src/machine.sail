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
  perm  : Perm,
  gen   : int
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
// the page and retries (PCIe ATS §4.2 / VT-d 5.20 §10).  `pending` is the
// request's pending bit: Set while the kernel has not yet resolved the fault,
// cleared when the page is mapped (`pri_resolve`), so the device's recheck
// (`pri_pending`) observes the resolution and retries the ATS translation.
// The queue is tagged by (did, pasid, iova); a device retries the same fault,
// it does not issue fresh requests (at most one entry per key).
struct PriRequest = {
  did     : int,
  pasid   : int,
  iova    : vaddr,
  pending : bool
}

// A queued-invalidation descriptor (VT-d IOTLB Invalidate / Invalidation-Wait,
// SMMU CMDQ, AMD-Vi command buffer).  is_wait = true is Invalidation-Wait (the
// completion barrier); is_wait = false is IotlbInvalidate va (a 4KiB selective
// IOTLB invalidation).  The circular-buffer head/tail MMIO is the weak-memory
// lift's job (S4.2b-2); here the queue is a plain FIFO list.
// The queued-invalidation command's granularity (VT-d 5.20 §6.5.2.3/§6.5.2.4):
// Gran_VA is the 4KiB-selective IotlbInvalidate (the existing command),
// Gran_PasidDid is the PASID-based-IOTLB Invalidate (P_IOTLB) PASID-selective
// granularity — drop the IOTLB entries associated with the specified (DID,
// PASID), the IOTLB half of the mandatory §6.5.2.2 PASID-cache -> IOTLB
// pairing.
enum InvalidationGran = {
  Gran_VA,
  Gran_PasidDid
}

struct InvalidationCmd = {
  is_wait : bool,
  gran    : InvalidationGran,
  va      : vaddr,
  did     : int,
  pasid   : int
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

// ---- IOTLB lookup + the walkers' fill-on-miss translation loops (S4.4/S4.5) ----
//
// The IOMMU caches completed translations in its IOTLB (keyed by
// (did, iova) — the SMMU keys by (SID, ASID, VA), AMD-Vi by (device_id,
// VA); the ASID is the IotlbEntry's pasid tag, 0 with no SVM).  The
// translation service loop replays the VT-d PASID-cache fill-on-miss shape
// (S4.5) for each walker: a hit answers from the cache without touching the
// page tables; a miss re-walks the tables, refills the IOTLB, and answers.
// The loop returns the translation and the resulting IOTLB, so after an
// invalidation the *loop* recovers — it re-walks and refills, unlike the raw
// evicted cache which misses (proved in smmu_proofs.v / amdvi_proofs.v).

val iotlb_lookup : (list(IotlbEntry), int, vaddr) -> option((paddr, Perm))
function iotlb_lookup(entries, did, va) = match entries {
  [||] => None(),
  e :: rest =>
    if e.did == did & vpn_of(e.iova) == vpn_of(va) then Some((e.pa, e.perm))
    else iotlb_lookup(rest, did, va)
}

val amdvi_translate_fill : (bits(44), list(IotlbEntry), PageTable, vaddr)
                        -> (option((paddr, Perm)), list(IotlbEntry))
function amdvi_translate_fill(root, iotlb, mem, iova) =
  match iotlb_lookup(iotlb, 0, iova) {
    Some(r) => (Some(r), iotlb),
    None() =>
      match amdvi_walk(root, mem, iova) {
        None() => (None(), iotlb),
        Some((pa, perm)) =>
          (Some((pa, perm)),
           struct { did = 0, pasid = 0, iova = iova, pa = pa, perm = perm, gen = 0 } :: iotlb)
      }
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

// The SMMU's fill-on-miss translation service loop: a hit answers from the
// IOTLB (keyed by the SID), a miss re-walks the STE -> CD -> two-stage
// tables and refills the IOTLB under (sid, gva).
val smmu_translate_fill : (list(Ste), list(Cd), int, list(IotlbEntry), PageTable, vaddr)
                       -> (option((paddr, Perm)), list(IotlbEntry))
function smmu_translate_fill(stes, cds, sid, iotlb, mem, gva) =
  match iotlb_lookup(iotlb, sid, gva) {
    Some(r) => (Some(r), iotlb),
    None() =>
      match smmu_translate(stes, cds, sid, mem, gva) {
        None() => (None(), iotlb),
        Some((pa, perm)) =>
          (Some((pa, perm)),
           struct { did = sid, pasid = 0, iova = gva, pa = pa, perm = perm, gen = 0 } :: iotlb)
      }
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
// cache entry is tagged by (DID, PASID) — the device plus process — and holds
// present + the resolved first-stage root: `pasid_cache_lookup` scans by tag
// equality (not by position), so the tag is part of the entry, eviction
// addresses entries by DID (device-selective invalidation), and refill
// re-installs the root under the full tag.  `pasid_cached_walk` is the
// two-stage walk with the cache standing in for the PASID table; the
// coherence invariant (`pasid_cache ⊆ pasid-table`) says a present cached
// root for (rid, pasid) matches the table, so `pasid_cached_walk =
// vtd_walk_pasid` (proved in vtd_proofs.v).
//
// The entry also carries a *generation* number (VT-d 5.20 §6.2.3: the PASID
// cache is tagged by (DID, PASID) — Table 17 — and the *generation* field is
// this model's mechanism for detecting a reused tag) so the hardware can
// detect a reused tag: when the kernel tears an address space down and a
// (DID, PASID) is
// reused with a fresh generation, the stale-generation entry must not answer
// (`pasid_cache_lookup_gen` misses it) until software evicts the tag conflict
// (`pasid_cache_evict_gen`) and refills under the new generation
// (`pasid_cache_refill_gen`).  The (DID, PASID)-keyed view — the walks and
// the fill-on-miss loops — is the generation-0 slice of the same cache.
struct PasidCacheEntry = {
  present : bool,
  did     : int,
  pasid   : int,
  gen     : int,
  s1_root : bits(44)
}

val pasid_cache_lookup : (list(PasidCacheEntry), (int, int)) -> option(PasidCacheEntry)
function pasid_cache_lookup(cache, dp) = match cache {
  [||] => None(),
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p then Some(e)
    else pasid_cache_lookup(rest, dp)
}

val pasid_cached_walk : (list(VtdContext), int, list(PasidCacheEntry), int, PageTable, vaddr) -> option((paddr, Perm))
function pasid_cached_walk(contexts, rid, cache, pasid, mem, iova) =
  match vtd_context_lookup(contexts, rid) {
    None() => None(),
    Some(c) =>
      if c.present then
        match pasid_cache_lookup(cache, (rid, pasid)) {
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
// DTE selects a context by index into the shared contexts list (whose SL root
// is the second-level root) and a PASID table by index into the device's
// PASID-table list (the DTE's PASID-table pointer / PTP):
// `vtd_walk_device` is the non-SVM walk (DTE -> context -> SL walk), and
// `vtd_walk_device_pasid` is the scalable-mode two-stage walk (DTE -> PASID
// table -> first-stage, then the selected context's second level).  Both
// reduce to the flat view exactly when the DTE points at the context/table
// the flat lookup would find (proved in vtd_proofs.v).
struct VtdDeviceEntry = {
  present   : bool,
  did       : int,
  ctx_index : int,
  pasid_tbl : int
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

// The device's PASID-table pointer: `tbls` is the device table's set of PASID
// tables, indexed by the DTE's `pasid_tbl` (VT-d 5.20 §3.4, PTP).
val pasid_table_lookup : (list(list(VtdPasid)), int) -> option(list(VtdPasid))
function pasid_table_lookup(tbls, idx) = match (tbls, idx) {
  (t :: _, 0) => Some(t),
  (_ :: rest, n) => pasid_table_lookup(rest, n - 1),
  ([||], _) => None()
}

// The scalable-mode two-stage walk: DTE -> PASID table -> first stage
// (guest, re-rooted at the PASID entry's s1_root), then the selected
// context's second level (GPA zero-extended for the stage-2 input).
val vtd_walk_device_pasid : (list(VtdDeviceEntry), list(list(VtdPasid)), list(VtdContext), int, int, PageTable, vaddr)
                         -> option((paddr, Perm))
function vtd_walk_device_pasid(devtbl, tbls, contexts, rid, pasid, mem, iova) =
  match vtd_device_lookup(devtbl, rid) {
    None() => None(),
    Some(d) =>
      if d.present then
        match pasid_table_lookup(tbls, d.pasid_tbl) {
          None() => None(),
          Some(ptes) =>
            match vtd_pasid_lookup(ptes, pasid) {
              None() => None(),
              Some(e) =>
                if e.present then
                  match iommu_walk(e.s1_root, mem, iova) {
                    None() => None(),
                    Some((gpa, _)) =>
                      match vtd_context_lookup(contexts, d.ctx_index) {
                        None() => None(),
                        Some(c) =>
                          if c.present then iommu_walk(c.sl_root, mem, sail_zero_extend(gpa, 64))
                          else None()
                      }
                  }
                else None()
            }
        }
      else None()
  }

// ---- PASID-cache eviction / refill (SSG-4 / S4.5) ----
//
// The PASID cache (VT-d 5.20 §15.4) is tagged by (DID, PASID): invalidation
// clears the cached first-stage root for a *device* — every entry whose DID
// matches turns non-present (device-selective invalidation), so the cached
// two-stage walk misses and the IOMMU must re-walk the PASID table; refill
// re-installs the table's root under the full (DID, PASID) tag.  Together
// with `pasid_cache_coherent` (the cache ⊆ table invariant), eviction is what
// *breaks* coherence and refill what *restores* it: the miss/refill cycle a
// translation after invalidation must go through.
// PASID-selective-within-domain PASID-cache invalidation (VT-d 5.20 §6.5.2.2,
// granularity 01b): clear only the (did, pasid) entry.  The granularity matrix
// of the PASID cache mirrors the IOTLB's (pasid/domain/ALL selectors): the
// PASID-cache Invalidate Descriptor's G field encodes Domain-Selective = 00b,
// PASID-Selective-within-Domain = 01b, Global = 11b, and 10b is Reserved
// (a reserved value makes the descriptor invalid).
val pasid_cache_evict_pasid : (list(PasidCacheEntry), (int, int)) -> list(PasidCacheEntry)
function pasid_cache_evict_pasid(cache, dp) = match cache {
  [||] => [||],
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p then
      struct { present = false, did = e.did, pasid = e.pasid, gen = e.gen, s1_root = e.s1_root } :: pasid_cache_evict_pasid(rest, dp)
    else e :: pasid_cache_evict_pasid(rest, dp)
}

// Global PASID-cache invalidation (VT-d 5.20 §6.5.2.2, granularity 11b):
// clear every entry, regardless of tag.  Domain-selective eviction
// (`pasid_cache_evict`, the 00b granularity) clears every entry of one DID.
// Per §6.5.2.2 software must always follow a PASID-cache invalidation with
// an IOTLB invalidation (Domain-Selective -> domain IOTLB, PASID-selective
// -> PASID-selective P_IOTLB, Global -> global IOTLB) — the pairing is
// proved as `iotlb_pasid_cache_pair_invalidate_clears` in iommu_proofs.v.
val pasid_cache_evict_all : list(PasidCacheEntry) -> list(PasidCacheEntry)
function pasid_cache_evict_all(cache) = match cache {
  [||] => [||],
  e :: rest =>
    struct { present = false, did = e.did, pasid = e.pasid, gen = e.gen, s1_root = e.s1_root } :: pasid_cache_evict_all(rest)
}

val pasid_cache_evict : (list(PasidCacheEntry), int) -> list(PasidCacheEntry)
function pasid_cache_evict(cache, did) = match cache {
  [||] => [||],
  e :: rest =>
    if e.did == did then
      struct { present = false, did = e.did, pasid = e.pasid, gen = e.gen, s1_root = e.s1_root } :: pasid_cache_evict(rest, did)
    else e :: pasid_cache_evict(rest, did)
}

val pasid_cache_refill : (list(PasidCacheEntry), (int, int), bits(44)) -> list(PasidCacheEntry)
function pasid_cache_refill(cache, dp, root) = match cache {
  [||] =>
    let (d, p) = dp in
    struct { present = true, did = d, pasid = p, gen = 0, s1_root = root } :: [||],
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p then
      struct { present = true, did = e.did, pasid = e.pasid, gen = e.gen, s1_root = root } :: rest
    else e :: pasid_cache_refill(rest, dp, root)
}

// ---- PASID-cache generation tags (SSG-4 / S4.5) ----
//
// The PASID cache tag is (DID, PASID) plus this model's *generation* field
// (VT-d 5.20 §6.2.3, Table 17: the tag is (DID, PASID) — the generation is
// the hardware's way of distinguishing reuses of a (DID, PASID) tag across
// address-space teardown, so a transaction issued under the *current*
// generation must not hit a stale-generation entry.  The (DID, PASID)-keyed
// view above is the
// generation-0 slice; the gen-tagged view below is the full tag.
// `pasid_cache_lookup_gen` answers only entries whose generation equals the
// current one; `pasid_cache_tag_conflict` detects a reused tag holding a
// stale generation (the hardware must not serve it); `pasid_cache_refill_gen`
// installs the root under the *current* generation (replacing the stale tag);
// and `pasid_cache_evict_gen` is the tag-conflict eviction — clear exactly
// the stale-generation entries of a reused tag, leaving a fresh-generation
// entry (and other tags) alone.

// Generation-tagged lookup: an entry answers iff its (did, pasid) matches AND
// its generation equals the current one g.
val pasid_cache_lookup_gen : (list(PasidCacheEntry), (int, int), int) -> option(PasidCacheEntry)
function pasid_cache_lookup_gen(cache, dp, g) = match cache {
  [||] => None(),
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p & e.gen == g then Some(e)
    else pasid_cache_lookup_gen(rest, dp, g)
}

// Tag conflict: a *present* entry for (did, pasid) whose generation differs
// from g — the tag was reused, so the old generation's usable (valid) cached
// root is stale and must not be served.  Non-present entries are already
// misses (the walks check `present`), so they are not conflicts.
val pasid_cache_tag_conflict : (list(PasidCacheEntry), (int, int), int) -> bool
function pasid_cache_tag_conflict(cache, dp, g) = match cache {
  [||] => false,
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p & e.present then
      if e.gen == g then pasid_cache_tag_conflict(rest, dp, g)
      else true
    else pasid_cache_tag_conflict(rest, dp, g)
}

// Generation-tagged refill: install the root under (did, pasid) with the
// *current* generation g.  A matching entry is updated in place (its tag now
// carries g, so the conflict it would have caused is gone); a fresh tag is
// prepended with generation g.
val pasid_cache_refill_gen : (list(PasidCacheEntry), (int, int), int, bits(44)) -> list(PasidCacheEntry)
function pasid_cache_refill_gen(cache, dp, g, root) = match cache {
  [||] =>
    let (d, p) = dp in
    struct { present = true, did = d, pasid = p, gen = g, s1_root = root } :: [||],
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p then
      struct { present = true, did = e.did, pasid = e.pasid, gen = g, s1_root = root } :: rest
    else e :: pasid_cache_refill_gen(rest, dp, g, root)
}

// Tag-conflict eviction: clear exactly the stale-generation entries of a
// reused (did, pasid) — an entry whose tag matches but whose generation
// differs from g.  A fresh-generation entry (gen = g) and all other tags
// survive.
val pasid_cache_evict_gen : (list(PasidCacheEntry), (int, int), int) -> list(PasidCacheEntry)
function pasid_cache_evict_gen(cache, dp, g) = match cache {
  [||] => [||],
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p & e.gen != g then
      struct { present = false, did = e.did, pasid = e.pasid, gen = e.gen, s1_root = e.s1_root } :: pasid_cache_evict_gen(rest, dp, g)
    else e :: pasid_cache_evict_gen(rest, dp, g)
}

// ---- PASID in-loop translation with fill-on-miss (SSG-4 / S4.5) ----
//
// The IOMMU's translation service loop: each request consults the PASID
// cache; a hit walks the cached first-stage root (the cache is untouched), a
// miss (an evicted or never-filled slot) re-walks the PASID table, refills
// the cache with the table's first-stage root, and walks.  The loop returns
// the translation and the resulting cache: after an eviction the *loop*
// recovers (it re-walks the table and refills, so it answers with the table
// result — unlike the raw evicted `pasid_cached_walk`, which misses) and the
// refilled cache is coherent again (`pasid_cache_refill_coherent`).  This is
// the functional in-loop lift; the weak-memory (gpfsl) program over the same
// loop is the next increment (see doc/iommu-shootdown-plan.md, S4.5).
val pasid_translate_fill : (list(VtdContext), int, list(VtdPasid), list(PasidCacheEntry), int, PageTable, vaddr)
                        -> (option((paddr, Perm)), list(PasidCacheEntry))
function pasid_translate_fill(contexts, rid, ptes, cache, pasid, mem, iova) =
  match pasid_cache_lookup(cache, (rid, pasid)) {
    None() => (None(), cache),
    Some(e) =>
      if e.present then
        (pasid_cached_walk(contexts, rid, cache, pasid, mem, iova), cache)
      else
        match vtd_pasid_lookup(ptes, pasid) {
          None() => (None(), cache),
          Some(te) =>
            if te.present then
              (vtd_walk_pasid(contexts, rid, ptes, pasid, mem, iova),
               pasid_cache_refill(cache, (rid, pasid), te.s1_root))
            else (None(), cache)
        }
  }

// Generation-tagged PASID-cache fill-on-miss (VT-d §6.2.3 / §6.5.2.2).
// The generation is a Tessera epoch tag for address-space reuse, not a field
// claimed to exist in the VT-d PASID-cache entry: a gen-g lookup may serve a
// cached entry only at g; a stale/missing tag re-reads the scalable-mode
// PASID table and refills the cache under g before walking the new root.
val pasid_translate_fill_gen : (list(VtdContext), int, list(VtdPasid), list(PasidCacheEntry), int,
                                PageTable, vaddr, int)
                              -> (option((paddr, Perm)), list(PasidCacheEntry))
function pasid_translate_fill_gen(contexts, rid, ptes, cache, pasid, mem, iova, g) =
  match pasid_cache_lookup_gen(cache, (rid, pasid), g) {
    Some(e) =>
      if e.present then
        (pasid_cached_walk(contexts, rid, cache, pasid, mem, iova), cache)
      else
        match vtd_pasid_lookup(ptes, pasid) {
          None() => (None(), cache),
          Some(te) =>
            if te.present then
              (vtd_walk_pasid(contexts, rid, ptes, pasid, mem, iova),
               pasid_cache_refill_gen(cache, (rid, pasid), g, te.s1_root))
            else (None(), cache)
        },
    None() =>
      match vtd_pasid_lookup(ptes, pasid) {
        None() => (None(), cache),
        Some(te) =>
          if te.present then
            (vtd_walk_pasid(contexts, rid, ptes, pasid, mem, iova),
             pasid_cache_refill_gen(cache, (rid, pasid), g, te.s1_root))
          else (None(), cache)
      }
  }

// ---- Device-table view of the PASID cache (SSG-4 / S4.5) ----
//
// In scalable mode the device table (DTE, indexed by requester ID) assigns the
// device its domain-id; the PASID cache is tagged (DID, PASID) (VT-d 5.20
// §15.4), so the device-table view keys the cache by the *DTE's* did rather
// than the raw requester ID.  `vtd_walk_device_pasid_cached` is the cached
// two-stage walk with the cache standing in for the device's PASID table;
// `vtd_device_translate_fill` is the fill-on-miss translation service loop
// over the device table — a hit walks the cached root, a miss re-walks the
// device's PASID table (selected by the DTE's `pasid_tbl` pointer), refills
// the cache under (d.did, pasid), and walks.
val vtd_walk_device_pasid_cached : (list(VtdDeviceEntry), list(list(VtdPasid)), list(VtdContext), int, int,
                                    list(PasidCacheEntry), PageTable, vaddr) -> option((paddr, Perm))
function vtd_walk_device_pasid_cached(devtbl, tbls, contexts, rid, pasid, cache, mem, iova) =
  match vtd_device_lookup(devtbl, rid) {
    None() => None(),
    Some(d) =>
      if d.present then
        match pasid_cache_lookup(cache, (d.did, pasid)) {
          None() => None(),
          Some(e) =>
            if e.present then
              match iommu_walk(e.s1_root, mem, iova) {
                None() => None(),
                Some((gpa, _)) =>
                  match vtd_context_lookup(contexts, d.ctx_index) {
                    None() => None(),
                    Some(c) =>
                      if c.present then iommu_walk(c.sl_root, mem, sail_zero_extend(gpa, 64))
                      else None()
                  }
              }
            else None()
        }
      else None()
  }

val vtd_device_translate_fill : (list(VtdDeviceEntry), list(list(VtdPasid)), list(VtdContext), int, int,
                                 list(PasidCacheEntry), PageTable, vaddr)
                             -> (option((paddr, Perm)), list(PasidCacheEntry))
function vtd_device_translate_fill(devtbl, tbls, contexts, rid, pasid, cache, mem, iova) =
  match vtd_device_lookup(devtbl, rid) {
    None() => (None(), cache),
    Some(d) =>
      if d.present then
        match pasid_cache_lookup(cache, (d.did, pasid)) {
          None() => (None(), cache),
          Some(e) =>
            if e.present then
              (vtd_walk_device_pasid_cached(devtbl, tbls, contexts, rid, pasid, cache, mem, iova), cache)
            else
              match pasid_table_lookup(tbls, d.pasid_tbl) {
                None() => (None(), cache),
                Some(ptes) =>
                  match vtd_pasid_lookup(ptes, pasid) {
                    None() => (None(), cache),
                    Some(te) =>
                      if te.present then
                        (vtd_walk_device_pasid(devtbl, tbls, contexts, rid, pasid, mem, iova),
                         pasid_cache_refill(cache, (d.did, pasid), te.s1_root))
                      else (None(), cache)
                  }
              }
        }
      else (None(), cache)
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

// ---- FRCDR drain-by-software (SSG-4 / S4.5) ----
//
// Software drains the FRCD queue to learn which endpoint / address faulted
// (VT-d 5.20 §6.1): `frcd_head` reads the oldest recorded fault, `frcd_clear`
// drops it (the head of the queue), and `frcd_drain` clears the whole queue
// — after which the interrupt line deasserts (`frcd_pending` is false) and
// the interrupt controller sees a no-op (proved in vtd_proofs.v).
val frcd_head : list(FrcdEntry) -> option(FrcdEntry)
function frcd_head(cache) = match cache {
  [||] => None(),
  e :: _ => Some(e)
}

val frcd_clear : list(FrcdEntry) -> list(FrcdEntry)
function frcd_clear(cache) = match cache {
  [||] => [||],
  _ :: rest => rest
}

val frcd_drain : list(FrcdEntry) -> list(FrcdEntry)
function frcd_drain(cache) = match cache {
  [||] => [||],
  _ :: rest => frcd_drain(rest)
}

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

// ---- invalidation granularity validity (S4.5 cross-check, §6.5.2.2/§6.5.2.4) ----
//
// A descriptor whose Granularity field holds a *reserved* encoding is an
// invalid descriptor.  For the PASID-cache Invalidate Descriptor (§6.5.2.2)
// the G field encodes Domain-Selective = 00b, PASID-Selective-within-Domain =
// 01b, Global = 11b, and 10b is Reserved.  For the P_IOTLB (§6.5.2.4) the G
// field encodes PASID-selective = 10b and Page-Selective-within-PASID = 11b;
// 00b and 01b are Reserved.  `granularity_valid` is the descriptor-acceptance
// check: a reserved encoding is rejected (treated as an invalid descriptor,
// the model's fault path), proved as the `granularity_valid_*` vectors.
val pasid_cache_inv_granularity_valid : bits(2) -> bool
function pasid_cache_inv_granularity_valid(g) = match g {
  0b00 => true,   // 00b Domain-Selective
  0b01 => true,   // 01b PASID-Selective-within-Domain
  0b11 => true,   // 11b Global
  _    => false   // 10b Reserved -> invalid descriptor
}

val p_iotlb_granularity_valid : bits(2) -> bool
function p_iotlb_granularity_valid(g) = match g {
  0b10 => true,   // 10b PASID-selective
  0b11 => true,   // 11b Page-Selective-within-PASID
  _    => false   // 00b/01b Reserved -> invalid descriptor
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
      (struct { did = did, pasid = 0, iova = iova, pa = pa, perm = perm, gen = 0 } :: iotlb,
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

// The device-side domain invalidation (AMD-Vi INVALIDATE_DEVTBL-SEL §2.4.7 /
// the SMMU stream-side tier of TLBI-by-domain): drop every endpoint
// device-TLB entry of a domain, regardless of IOVA — the DevTlbEntry-granular
// twin of `iotlb_invalidate_domain`.
val ats_invalidate_domain : (list(DevTlbEntry), int) -> list(DevTlbEntry)
function ats_invalidate_domain(devtlbs, did) = match devtlbs {
  [||] => [||],
  e :: rest =>
    if e.did == did then ats_invalidate_domain(rest, did)
    else e :: ats_invalidate_domain(rest, did)
}

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

// ---- VT-d P_IOTLB PASID-selective invalidation (SSG-4 / S4.5) ----
//
// The PASID-based-IOTLB Invalidate Descriptor (VT-d 5.20 §6.5.2.4) is how
// software invalidates IOTLB *and* paging-structure-cache entries after
// changing first-stage tables.  Its PASID-selective granularity (G = 10b)
// drops the entries *associated with the specified PASID and domain-id* —
// both tags, unlike the SMMU TLBI-by-ASID (`iotlb_invalidate_pasid`, pasid
// only).  This is the IOTLB half of the mandatory PASID-cache -> IOTLB
// pairing (§6.5.2.2): a PASID-selective-within-domain PASID-cache
// invalidation (01b) must be followed by a PASID-selective P_IOTLB
// invalidation, proved as `iotlb_pasid_cache_pair_invalidate_clears`.
val iotlb_invalidate_pasid_did : (list(IotlbEntry), (int, int)) -> list(IotlbEntry)
function iotlb_invalidate_pasid_did(entries, dp) = match entries {
  [||] => [||],
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p then iotlb_invalidate_pasid_did(rest, dp)
    else e :: iotlb_invalidate_pasid_did(rest, dp)
}

// ---- IOTLB generation tags (SSG-4 / S4.5, SMMU/AMD-Vi replay) ----
//
// The gen-tagged IOTLB view, the translation-cache twin of the PASID-cache
// generation machinery: an IotlbEntry carries the *generation* its (did,
// pasid) tag was filled under, so a reused tag across address-space teardown
// (the first-stage root changed: a new SMMU CD / a new AMD-Vi PASID-table
// root for the same (SID, ASID) / (0, PASID)) does not answer stale cached
// translations.  `iotlb_lookup_gen` answers iff the (did, pasid, IOVA page)
// tag matches AND the entry's generation equals the current one g;
// `iotlb_tag_conflict` detects a reused tag holding a stale generation (any
// (did, pasid) entry with gen != g); `iotlb_refill_gen` installs the fresh
// translation under (did, pasid, iova) with generation g; `iotlb_evict_gen`
// clears exactly the stale-generation entries of the reused tag.  The
// generation-0 slice — `iotlb_lookup` / the fill loops below — is the
// legacy view of the same cache.
val iotlb_lookup_gen : (list(IotlbEntry), (int, int), vaddr, int) -> option((paddr, Perm))
function iotlb_lookup_gen(entries, dp, va, g) = match entries {
  [||] => None(),
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p & vpn_of(e.iova) == vpn_of(va) & e.gen == g then Some((e.pa, e.perm))
    else iotlb_lookup_gen(rest, dp, va, g)
}

val iotlb_tag_conflict : (list(IotlbEntry), (int, int), int) -> bool
function iotlb_tag_conflict(entries, dp, g) = match entries {
  [||] => false,
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p then
      if e.gen == g then iotlb_tag_conflict(rest, dp, g)
      else true
    else iotlb_tag_conflict(rest, dp, g)
}

val iotlb_refill_gen : (list(IotlbEntry), (int, int), vaddr, int, paddr, Perm) -> list(IotlbEntry)
function iotlb_refill_gen(entries, dp, va, g, pa, perm) = match entries {
  [||] =>
    let (d, p) = dp in
    struct { did = d, pasid = p, iova = va, pa = pa, perm = perm, gen = g } :: [||],
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p & vpn_of(e.iova) == vpn_of(va) then
      struct { did = e.did, pasid = e.pasid, iova = e.iova, pa = pa, perm = perm, gen = g } :: rest
    else e :: iotlb_refill_gen(rest, dp, va, g, pa, perm)
}

val iotlb_evict_gen : (list(IotlbEntry), (int, int), int) -> list(IotlbEntry)
function iotlb_evict_gen(entries, dp, g) = match entries {
  [||] => [||],
  e :: rest =>
    let (d, p) = dp in
    if e.did == d & e.pasid == p & e.gen != g then iotlb_evict_gen(rest, dp, g)
    else e :: iotlb_evict_gen(rest, dp, g)
}

// The generation-aware SMMU / AMD-Vi fill loops: the walker consults the
// *gen-tagged* IOTLB (a stale-generation entry is a miss) and refills under
// the current generation g.  After a first-stage root change software bumps
// g (a new CD / PASID-table root epoch), so the stale cached translations
// cannot answer — the loop re-walks and refills under g (the SMMU/AMD-Vi
// twin of the PASID-cache tag-conflict eviction).
val smmu_translate_fill_gen : (list(Ste), list(Cd), int, list(IotlbEntry), PageTable, vaddr, int)
  -> (option((paddr, Perm)), list(IotlbEntry))
function smmu_translate_fill_gen(stes, cds, sid, iotlb, mem, gva, g) =
  match iotlb_lookup_gen(iotlb, (sid, 0), gva, g) {
    Some(r) => (Some(r), iotlb),
    None() =>
      match smmu_translate(stes, cds, sid, mem, gva) {
        None() => (None(), iotlb),
        Some((pa, perm)) =>
          (Some((pa, perm)), iotlb_refill_gen(iotlb, (sid, 0), gva, g, pa, perm))
      }
  }

val amdvi_translate_fill_gen : (bits(44), list(IotlbEntry), PageTable, vaddr, int)
  -> (option((paddr, Perm)), list(IotlbEntry))
function amdvi_translate_fill_gen(root, iotlb, mem, iova, g) =
  match iotlb_lookup_gen(iotlb, (0, 0), iova, g) {
    Some(r) => (Some(r), iotlb),
    None() =>
      match amdvi_walk(root, mem, iova) {
        None() => (None(), iotlb),
        Some((pa, perm)) =>
          (Some((pa, perm)), iotlb_refill_gen(iotlb, (0, 0), iova, g, pa, perm))
      }
  }

// ---- queued invalidation (SSG-4 / S4.2b + S4.5 P_IOTLB) ----
//
// The IOMMU's command-queue drain: process the FIFO in order, applying each
// command to the IOTLB, and complete (Some iotlb) when an Invalidation-Wait
// is reached — the Invalidation-Wait completion (VT-d §6.5.2.9) that orders
// the prior invalidations.  A queue with no wait descriptor drains to None
// (no completion).  The Gran_VA command is the 4KiB IotlbInvalidate
// (§6.5.2.3); the Gran_PasidDid command is the P_IOTLB PASID-selective
// (§6.5.2.4) — drop the (DID, PASID)-associated IOTLB entries, the IOTLB
// half of the mandatory §6.5.2.2 PASID-cache -> IOTLB pairing.
val iommu_process_queue : (list(InvalidationCmd), list(IotlbEntry)) -> option(list(IotlbEntry))
function iommu_process_queue(queue, iotlb) = match queue {
  [||] => None(),
  c :: rest =>
    if c.is_wait then Some(iotlb)
    else match c.gran {
      Gran_VA => iommu_process_queue(rest, iotlb_invalidate(iotlb, c.va)),
      Gran_PasidDid => iommu_process_queue(rest, iotlb_invalidate_pasid_did(iotlb, (c.did, c.pasid)))
    }
}

// PRI page request: enqueue a request to map the page, tagged by
// (did, pasid, iova) (at most one entry per key — a device retries the same
// fault, it does not issue fresh ones).  Re-issuing an outstanding request
// re-pends it (the entry's pending bit is Set again), so the queue stays
// pending for the duration of the fault.
val pri_request : (list(PriRequest), (int, int), vaddr) -> list(PriRequest)
function pri_request(prireqs, dp, iova) = match prireqs {
  [||] =>
    let (d, p) = dp in
    struct { did = d, pasid = p, iova = iova, pending = true } :: [||],
  r :: rest =>
    let (d, p) = dp in
    if r.did == d & r.pasid == p & r.iova == iova then
      struct { did = r.did, pasid = r.pasid, iova = r.iova, pending = true } :: rest
    else r :: pri_request(rest, dp, iova)
}

// The PRI recheck: find the request for (did, pasid, iova).
val pri_lookup : (list(PriRequest), (int, int), vaddr) -> option(PriRequest)
function pri_lookup(prireqs, dp, iova) = match prireqs {
  [||] => None(),
  r :: rest =>
    let (d, p) = dp in
    if r.did == d & r.pasid == p & r.iova == iova then Some(r)
    else pri_lookup(rest, dp, iova)
}

// The pending-bit recheck: is the request for (did, pasid, iova) still
// outstanding?  The device's retry loop spins on this bit: Set means the
// kernel has not resolved the page fault yet.
val pri_pending : (list(PriRequest), (int, int), vaddr) -> bool
function pri_pending(prireqs, dp, iova) = match pri_lookup(prireqs, dp, iova) {
  None() => false,
  Some(r) => r.pending
}

// The kernel mapped the page: clear the request's pending bit, so the
// device's recheck observes the resolution and its next ATS translation
// succeeds (PCIe ATS §4.2, the page is now resident).
val pri_resolve : (list(PriRequest), (int, int), vaddr) -> list(PriRequest)
function pri_resolve(prireqs, dp, iova) = match prireqs {
  [||] => [||],
  r :: rest =>
    let (d, p) = dp in
    if r.did == d & r.pasid == p & r.iova == iova then
      struct { did = r.did, pasid = r.pasid, iova = r.iova, pending = false } :: rest
    else r :: pri_resolve(rest, dp, iova)
}

// The fault-message path of PRI (VT-d 5.20 §7.2 / §10.4.14): when the
// device's request is pending and the translation faults, the fault record
// (DID, PASID, IOVA, reason) is produced — delivered into the FRCD via
// `frcd_record`, so the fault-message interrupt names the faulting endpoint.
val pri_fault_delivers : (list(PriRequest), (int, int), vaddr, FaultReason) -> option(FaultRecord)
function pri_fault_delivers(prireqs, dp, iova, reason) =
  if pri_pending(prireqs, dp, iova) then
    let (d, p) = dp in
    Some(struct { did = d, pasid = p, iova = iova, reason = reason })
  else None()

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

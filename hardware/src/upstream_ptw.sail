// Tessera — G1 trust-line: upstream pt_walk from sail-riscv vmem.sail
// Minimal Sv39 fragment: walk control flow only (no permission check, no A/D
// update, no TLB, no callbacks).  Externs stubbed for the Sv39 fragment.
// SPDX-License-Identifier: BSD-2-Clause

default Order dec

$include <prelude.sail>

// ---- result type (Sail reserved name 'result', so we use 'ptw_res') ----
union ptw_res('a: Type, 'b: Type) = {
  Ok  : 'a,
  Err : 'b
}

mapping bool_bit : bool <-> bits(1) = { false <-> 0b0, true <-> 0b1 }
val not : bool -> bool
function not(b) = not_bool(b)

// ---- PTE types (from vmem_pte.sail) ----
type pte_flags_bits = bits(8)
type pte_ext_bits   = bits(10)

bitfield PTE_Flags : pte_flags_bits = {
  D : 7, A : 6, G : 5, U : 4, X : 3, W : 2, R : 1, V : 0
}

bitfield PTE_Ext : pte_ext_bits = {
  N : 9, PBMT : 8 .. 7, RSW_60t59b : 6 .. 5, reserved : 4 .. 0
}

let default_sv32_ext_pte : pte_ext_bits = 0b0000000000

val ext_bits_of_PTE : forall 'pte_size, 'pte_size in {32, 64}. bits('pte_size) -> PTE_Ext
function ext_bits_of_PTE(pte) =
  Mk_PTE_Ext(if 'pte_size == 64 then pte[63 .. 54] else default_sv32_ext_pte)

val PPN_of_PTE : forall 'pte_size, 'pte_size in {32, 64}.
  bits('pte_size) -> bits(if 'pte_size == 32 then 22 else 44)
function PPN_of_PTE(pte) = if 'pte_size == 32 then pte[31 .. 10] else pte[53 .. 10]

// ---- PTE predicates (from upstream_vmem_pte.sail) ----

val pte_is_non_leaf : PTE_Flags -> bool
function pte_is_non_leaf(pte_flags) =
    pte_flags[X] == 0b0 & pte_flags[W] == 0b0 & pte_flags[R] == 0b0

val pte_is_invalid : (PTE_Flags, PTE_Ext) -> bool
function pte_is_invalid(pte_flags, pte_ext) =
    pte_flags[V] == 0b0
  | (pte_flags[R] == 0b0 & pte_flags[W] == 0b1 & pte_flags[X] == 0b0)
  | (pte_flags[R] == 0b0 & pte_flags[W] == 0b1 & pte_flags[X] == 0b1)
  | (
      pte_is_non_leaf(pte_flags) & (pte_flags[A] == 0b1 | pte_flags[D] == 0b1 | pte_flags[U] == 0b1 | pte_ext.bits != 0b0000000000)
    | pte_ext[PBMT]       != 0b00
    | pte_ext[RSW_60t59b] != 0b00
    | pte_ext[reserved] != 0b00000
  )

// ---- PTW error type (vmem_ptw.sail) ----
union PTW_Error = {
  PTW_Invalid_Addr     : unit,
  PTW_No_Access        : unit,
  PTW_Invalid_PTE      : unit,
  PTW_No_Permission    : unit,
  PTW_Misaligned       : unit,
  PTW_PTE_Needs_Update : unit,
  PTW_Ext_Error        : unit
}

// ---- page_based_mem_type (vmem_types.sail) ----
enum page_based_mem_type = { PBMT_PMA, PBMT_NC, PBMT_IO }

// ---- PTW output (vmem.sail ll.26-37) ----
struct PTW_Output = {
  ppn     : bits(44),
  pte     : bits(64),
  pteAddr : bits(56),
  level   : range(0, 2),
  pbmt    : page_based_mem_type,
  global  : bool
}

// ---- address arithmetic (Sv39) ----
val pte_address_sw : (bits(44), bits(9)) -> bits(56)
function pte_address_sw(table_ppn, index) =
  sail_shiftleft(sail_zero_extend(table_ppn, 56), 12) | sail_shiftleft(sail_zero_extend(index, 56), 3)

// ---- read_pte: parameterized via association-list memory ----
type Mem = list((bits(56), bits(64)))

val read_pte_sw : (Mem, bits(56)) -> option(bits(64))
function read_pte_sw(mem, addr) =
  match mem {
    [||] => None(),
    pair :: rest =>
      match pair {
        (a, v) => if a == addr then Some(v) else read_pte_sw(rest, addr)
      }
  }

// ---- extension stubs (Sv39 fragment) ----
enum Extension = { Ext_Svnapot, Ext_Sv39 }

val currentlyEnabled : Extension -> bool
function currentlyEnabled(e) = match e {
  Ext_Sv39    => true,
  Ext_Svnapot => true
}

// ---- pt_walk: verbatim from vmem.sail ll.101-207, Sv39 fragment ----
val pt_walk : (Mem, bits(27), bits(44), range(0, 2)) -> ptw_res(PTW_Output, PTW_Error)
function pt_walk(mem, vpn, pt_base, level) = {
  let vpn_i_size = 9;
  let vpn_i = vpn[(level + 1) * vpn_i_size - 1 .. level * vpn_i_size];
  let pte_addr = pt_base @ vpn_i @ 0b000;

  match read_pte_sw(mem, pte_addr) {
    None() => Err(PTW_No_Access()),
    Some(pte) => {
      let pte_flags = Mk_PTE_Flags(pte[7 .. 0]);
      let pte_ext   = ext_bits_of_PTE(pte);

      if pte_is_invalid(pte_flags, pte_ext) then {
        Err(PTW_Invalid_PTE())
      }
      else {
        let ppn = PPN_of_PTE(pte);
        if pte_is_non_leaf(pte_flags) then {
          if level > 0 then
            pt_walk(mem, vpn, ppn, level - 1)
          else
            Err(PTW_Invalid_PTE())
        } else {
          // Check misaligned superpage (level > 0 only, explicit match)
          if level == 2 then {
            if ppn[17 .. 0] != 0b000000000000000000 then
              return Err(PTW_Misaligned());
          } else if level == 1 then {
            if ppn[8 .. 0] != 0b000000000 then
              return Err(PTW_Misaligned());
          };

          // NAPOT: only at level 0 (level > 0 NAPOT is reserved)
          let final_ppn =
            if currentlyEnabled(Ext_Svnapot) & pte_ext[N] == 0b1 then {
              let pte_napot_bits = 4;
              if ppn[pte_napot_bits - 1 .. 0] != 0b1000 then
                return Err(PTW_Invalid_PTE());
              [ppn with (pte_napot_bits - 1) .. 0 = vpn[pte_napot_bits - 1 .. 0]]
            } else {
              ppn
            };

          let pbmt = PBMT_PMA;

          Ok(struct {
            ppn = final_ppn,
            pte = pte,
            pteAddr = pte_addr,
            level = level,
            pbmt = pbmt,
            global = false
          })
        }
      }
    }
  }
}



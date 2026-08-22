// Tessera — G1 trust-line: upstream pt_walk from sail-riscv vmem.sail
// Minimal Sv39 fragment. SPDX-License-Identifier: BSD-2-Clause
default Order dec
$include <prelude.sail>

union ptw_res('a: Type, 'b: Type) = { Ok : 'a, Err : 'b }

mapping bool_bit : bool <-> bits(1) = { false <-> 0b0, true <-> 0b1 }
val not : bool -> bool
function not(b) = not_bool(b)

type pte_flags_bits = bits(8)
type pte_ext_bits   = bits(10)
bitfield PTE_Flags : pte_flags_bits = { D : 7, A : 6, G : 5, U : 4, X : 3, W : 2, R : 1, V : 0 }
bitfield PTE_Ext : pte_ext_bits = { N : 9, PBMT : 8 .. 7, RSW_60t59b : 6 .. 5, reserved : 4 .. 0 }
let default_sv32_ext_pte : pte_ext_bits = 0b0000000000

val ext_bits_of_PTE : forall 'pte_size, 'pte_size in {32, 64}. bits('pte_size) -> PTE_Ext
function ext_bits_of_PTE(pte) = Mk_PTE_Ext(if 'pte_size == 64 then pte[63 .. 54] else default_sv32_ext_pte)

val PPN_of_PTE : forall 'pte_size, 'pte_size in {32, 64}. bits('pte_size) -> bits(if 'pte_size == 32 then 22 else 44)
function PPN_of_PTE(pte) = if 'pte_size == 32 then pte[31 .. 10] else pte[53 .. 10]

val pte_is_non_leaf : PTE_Flags -> bool
function pte_is_non_leaf(f) = f[X] == 0b0 & f[W] == 0b0 & f[R] == 0b0

val pte_is_invalid : (PTE_Flags, PTE_Ext) -> bool
function pte_is_invalid(f, e) =
    f[V] == 0b0
  | (f[R] == 0b0 & f[W] == 0b1 & f[X] == 0b0)
  | (f[R] == 0b0 & f[W] == 0b1 & f[X] == 0b1)
  | (pte_is_non_leaf(f) & (f[A] == 0b1 | f[D] == 0b1 | f[U] == 0b1 | e.bits != 0b0000000000)
    | e[PBMT] != 0b00 | e[RSW_60t59b] != 0b00 | e[reserved] != 0b00000)

enum PTW_Error = { PTW_No_Access, PTW_Invalid_PTE, PTW_Misaligned }
enum page_based_mem_type = { PBMT_PMA, PBMT_NC, PBMT_IO }
struct PTW_Output = { ppn : bits(44), pte : bits(64), pteAddr : bits(56), level : range(0, 2), pbmt : page_based_mem_type, global : bool }

type Mem = list((bits(56), bits(64)))

val read_pte_sw : (Mem, bits(56)) -> option(bits(64))
function read_pte_sw(mem, addr) = match mem { [||] => None(), pair :: rest => match pair { (a, v) => if a == addr then Some(v) else read_pte_sw(rest, addr) } }

enum Extension = { Ext_Svnapot, Ext_Sv39 }
val currentlyEnabled : Extension -> bool
function currentlyEnabled(e) = match e { Ext_Sv39 => true, Ext_Svnapot => true }

val pt_walk : (Mem, bits(27), bits(44), range(0, 2)) -> ptw_res(PTW_Output, PTW_Error)
function pt_walk(mem, vpn, pt_base, level) = {
  let vpn_i_size = 9;
  let vpn_i = vpn[(level + 1) * vpn_i_size - 1 .. level * vpn_i_size];
  let pte_addr = pt_base @ vpn_i @ 0b000;
  match read_pte_sw(mem, pte_addr) {
    None() => Err(PTW_No_Access),
    Some(pte) => {
      let pte_flags = Mk_PTE_Flags(pte[7 .. 0]);
      let pte_ext = ext_bits_of_PTE(pte);
      if pte_is_invalid(pte_flags, pte_ext) then Err(PTW_Invalid_PTE)
      else {
        let ppn = PPN_of_PTE(pte);
        if pte_is_non_leaf(pte_flags) then {
          if level > 0 then pt_walk(mem, vpn, ppn, level - 1)
          else Err(PTW_Invalid_PTE)
        } else {
          if level == 2 & ppn[17 .. 0] != 0b000000000000000000 then return Err(PTW_Misaligned);
          if level == 1 & ppn[8 .. 0] != 0b000000000 then return Err(PTW_Misaligned);
          let final_ppn = if currentlyEnabled(Ext_Svnapot) & pte_ext[N] == 0b1 then
            if ppn[3 .. 0] != 0b1000 then return Err(PTW_Invalid_PTE)
            else [ppn with 3 .. 0 = vpn[3 .. 0]]
          else ppn;
          Ok(struct { ppn = final_ppn, pte = pte, pteAddr = pte_addr, level = level, pbmt = PBMT_PMA, global = false })
        }
      }
    }
  }
}
termination_measure pt_walk(_,_,_,level) = level

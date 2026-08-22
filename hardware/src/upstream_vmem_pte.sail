// Tessera — G1 trust-line: upstream PTE predicates from sail-riscv vmem_pte.sail
// Self-contained Sv39 fragment with all externs stubbed and simplified.
// SPDX-License-Identifier: BSD-2-Clause

default Order dec

$include <prelude.sail>

mapping bool_bit : bool <-> bits(1) = {
  false  <-> 0b0,
  true   <-> 0b1
}

val not : bool -> bool
function not(b) = not_bool(b)

val bit_to_bool : bits(1) -> bool
function bit_to_bool(x) = bool_bit(x)

// === Verbatim from vmem_pte.sail ll.21-109 (with Sv39 simplifications) ===

type pte_flags_bits = bits(8)
type pte_ext_bits   = bits(10)

bitfield PTE_Ext : pte_ext_bits = {
  N          : 9,
  PBMT       : 8 .. 7,
  RSW_60t59b : 6 .. 5,
  reserved   : 4 .. 0,
}

let default_sv32_ext_pte : pte_ext_bits = 0b0000000000

val ext_bits_of_PTE : forall 'pte_size, 'pte_size in {32, 64}. bits('pte_size) -> PTE_Ext
function ext_bits_of_PTE(pte) =
  Mk_PTE_Ext(if 'pte_size == 64 then pte[63 .. 54] else default_sv32_ext_pte)

val PPN_of_PTE : forall 'pte_size, 'pte_size in {32, 64}.
  bits('pte_size) -> bits(if 'pte_size == 32 then 22 else 44)
function PPN_of_PTE(pte) = if 'pte_size == 32 then pte[31 .. 10] else pte[53 .. 10]

bitfield PTE_Flags : pte_flags_bits = {
  D : 7,
  A : 6,
  G : 5,
  U : 4,
  X : 3,
  W : 2,
  R : 1,
  V : 0
}

val pte_is_non_leaf : PTE_Flags -> bool
function pte_is_non_leaf(pte_flags) =
    pte_flags[X] == 0b0
  & pte_flags[W] == 0b0
  & pte_flags[R] == 0b0

// pte_is_invalid from vmem_pte.sail ll.89-109, simplified for the Sv39 fragment:
// - menvcfg.SSE=0 → write-only (R=0,W=1,X=0) clause fires (no guard)
// - currentlyEnabled(Ext_Svpbmt)=false → PBMT forwards-match clause dead
// - currentlyEnabled(Ext_Svnapot)=true → N!=0 & not(true)=false → NAPOT clause dead
// - currentlyEnabled(Ext_Svrsw60t59b)=false → RSW!=0 & not(false)=true → RSW clause fires
// - pte_reserved_bits_must_be_zero=true (Privileged ISA >= 1.12)
val pte_is_invalid : (PTE_Flags, PTE_Ext) -> bool
function pte_is_invalid(pte_flags, pte_ext) =
    pte_flags[V] == 0b0
  | (pte_flags[R] == 0b0 & pte_flags[W] == 0b1 & pte_flags[X] == 0b0)   // SSE=0: write-only reserved
  | (pte_flags[R] == 0b0 & pte_flags[W] == 0b1 & pte_flags[X] == 0b1)   // R=0,W=1,X=1 reserved
  | (                                                                     // reserved-bits-must-be-zero
      pte_is_non_leaf(pte_flags) & (pte_flags[A] == 0b1 | pte_flags[D] == 0b1 | pte_flags[U] == 0b1 | pte_ext.bits != 0b0000000000)
    | pte_ext[PBMT]       != 0b00                                         // PBMTE=0: PBMT!=0 reserved
    | pte_ext[RSW_60t59b] != 0b00                                         // Svrsw60t59b disabled: RSW!=0 reserved
    | pte_ext[reserved] != 0b00000                                        // reserved must be zero
  )
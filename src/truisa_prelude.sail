/*=======================================================================================*/
/*  TRUISA RISCV Sail Model                                                              */
/*                                                                                       */
/*  This TRUISA Sail RISC-V architecture model here, comprising all files and            */
/*  directories except for the snapshots of the Lem and Sail libraries in the            */
/*  prover_snapshots directory (which include copies of their licenses), is subject      */
/*  to the BSD two-clause licence below.                                                 */
/*                                                                                       */
/*  Copyright (c) 2019-2025                                                              */
/*    Dong Tong, Peking University                                                       */
/*                                                                                       */
/*=======================================================================================*/

/* TRUISA specific helpers */

val MEMr_tag = "read_tag_bool"  : bits(64) -> bool
val MEMw_tag = "write_tag_bool" : (bits(64) , bool) -> unit

val MAX : forall 'n, 'n >= 0 . atom('n) -> atom(2 ^ 'n - 1)
function MAX(n) = pow2(n) - 1

/*!
 * align_down(n, bv) returns the given bit vector, bv,  aligned down to a power
 * of two by clearing the least significant n bits.
 */
val align_down : forall 'n 'm, 'n >= 1 & 'm > 'n . (int('n), bits('m)) -> bits('m)
function align_down(n, bv) = [bv with ('n - 1) .. 0 = zeros()]

/* CSR 0x080 */
bitfield DLBEntryBound： bits(32) = {
    radix : 30..26,
    W: 25,
    bound: 24..0,
}

/* CSR 0x081 */
bitfield DLBEntryBase： bits(32) = {
    L: 31, // Locked
    G: 30, // Granularity. 0: Byte, 1: 128B Alignment
    X: 28, // Instruciton execution
    R: 26, // Write
    Base: 24..0,
}

let DLBNumEntries = 8
type DLBIndexT = (bits(3))
let DLBIndexMax : DLBIndexT = 0b111

bitfield DLBEntry : bits(57) = {
  radix    : 59..55,
  W        : 54,
  bound    : 53..29,
  L        : 28,
  G        : 27,
  X        : 26,
  R        : 25,
  base     : 24..0,
}

register DLBIndex : DLBIndexT
register DLBFIFO : DLBIndexT
register CSR_DLBEntryBase : DLBEntryBase
register CSR_DLBEntryBound : DLBEntryBound

reigster DLBEntry00 ： DLBEntry
reigster DLBEntry01 ： DLBEntry
reigster DLBEntry02 ： DLBEntry
reigster DLBEntry03 ： DLBEntry
reigster DLBEntry04 ： DLBEntry
reigster DLBEntry05 ： DLBEntry
reigster DLBEntry06 ： DLBEntry
reigster DLBEntry07 ： DLBEntry

let DLBEntries : vector(DLBNumEntries, dec, register(DLBEntry)) = {
    ref DLBEntry07,
    ref DLBEntry06,
    ref DLBEntry05,
    ref DLBEntry04,
    ref DLBEntry03,
    ref DLBEntry02,
    ref DLBEntry01,
    ref DLBEntry00
}
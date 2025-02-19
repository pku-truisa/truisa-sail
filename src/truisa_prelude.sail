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

/* CSR 0x0A0 */
bitfield DLBEntryBaseReg： bits(32) = {
    mode: 31,
    radix : 30..26,
    w_flag : 25,
    base: 24..0,
}

/* CSR 0x0B0 */
bitfield DLBEntryBoundReg： bits(32) = {
    reserved: 31..25,
    bound: 24..0,
}

let DLBNumEntries = 8
type DLBIndexT = (bits(3))
let DLBIndexMax : DLBIndexT = 0b111

bitfield DLBEntry : bits(57) = {
  mode     : 56,
  radix    : 55..51, 
  w_flag   : 50
  base     : 49..25,
  bound    : 24..0,
}

register DLBIndex : DLBIndexT
register DLBRandom : DLBIndexT
register DLBEntryBase : DLBEntryBaseReg
register DLBEntryBound : DLBEntryBoundReg

reigster DLBEntry00 ： TLBEntry
reigster DLBEntry01 ： TLBEntry
reigster DLBEntry02 ： TLBEntry
reigster DLBEntry03 ： TLBEntry
reigster DLBEntry04 ： TLBEntry
reigster DLBEntry05 ： TLBEntry
reigster DLBEntry06 ： TLBEntry
reigster DLBEntry07 ： TLBEntry

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
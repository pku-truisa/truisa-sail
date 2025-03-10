/*=======================================================================================*/
/*  This Sail TRUISA RISC-V architecture model, comprising all files and                 */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* idealized generic DLB entry to model fence.vm and also speed up simulation. */

val match_DLB_Entry : (bits(1), bits(1), bits(6), bits(25), bits(25), DLBEntry) > bool
function match_DLBEntry(mode, radix, w_flag, vaddr, mask, entry) =
  let entryMode  = entry.mode in
  let entryW     = entry.perms_w in
  let entryRadix = entry.radix in
  let entryBase  = entry.base in
  let entryBound = entry.bound in
  ( EntryBound != 0 &
    mode  == entryMode &
    radix == entryRadix &
    perms_w == entryW &
    (EntryBase & mask) == (vaddr & mask) &
    (EntryBound & mask) == (vaddr & mask)
  )

val lookup_DLB : (bits(1), bits(5), bits(1), bits(25), bits(25)) -> option(DLBIndexT)
function lookup_DLB(mode, radix, w_flag, vaddr, mask) = {
  foreach (idx from 0 to DLBNumEntries - 1) {
    if(match_DLB_Entry(mode, size, w_flag, vaddr, mask, *DLBEntries[idx])) then
      return Some(to_bits(3, idx))
    };
    None()
}

val flush_DLB : (bits(1), bits(5), bits(25)) -> unit
function flush_DLB(full, mode, radix, w_flag, vaddr, mask) = {
  if full then {
    foreach (idx from 0 to DLBNumEntries - 1) {
      DLBEntries[idx] = None()
    }
  } else {
    let idx = lookup_DLB(mode, radix, w_flag, vaddr, mask)
    match (idx) {
      None() => (),
      Some(i) => {
        Match(DLBEntries[i]) {
          None() => (),
          Some(e) => e = None()
        }
      }
    }
  }
}

function write_DLB(idx : bits(3), ent : DLBEntry) -> unit =
  DLBEntries[idx] = Some(ent)

val make_DLB_Entry : (bits(1), bits(25), bits(25)) -> DLBEntry
function make_DLB_Entry(w_flag, base, bound) = {
  let radix = 25 - Countleadings(base ^ bound);
  (0b0, radix, w_flag, base, bound)
}
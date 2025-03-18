/*=======================================================================================*/
/*  Truisa RISCV Sail Model                                                              */
/*                                                                                       */
/*  Copyright (c) 2017-2025                                                              */
/*    Dong Tong, Peking University                                                       */
/*=======================================================================================*/

/* merged or split register file? (split not yet implemented) */
let haveSplitRegFile = false

/* register type */
type regtype = Capability

/* null cap */
let zero_reg : regtype = null_cap

/* register printer */
val RegStr : Capability -> string
function RegStr(r) = capToString(r)

/* conversions */

val regval_from_reg : regtype -> xlenbits
function regval_from_reg(r) = address_to_int(r.address)

val regval_into_reg : xlenbits -> regtype
function regval_into_reg(v) = {null_cap with address = int_to_address(v)}

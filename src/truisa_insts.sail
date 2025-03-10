/*=======================================================================================*/
/*  Truisa RISCV Sail Model                                                              */
/*                                                                                       */
/*  Copyright (c) 2017-2025                                                              */
/*    Dong Tong, Peking University                                                       */
/*=======================================================================================*/

/* Capability versions of mode-dependent instructions */

/* Operations that extract parts of a capability into GPR */

union clause ast = CGetPerm   : (regidx, regidx)
union clause ast = CGetBase   : (regidx, regidx)
union clause ast = CGetAddr   : (regidx, regidx)
union clause ast = CGetBound  : (regidx, regidx)

/*!
 * The least significant bits of integer register *rd* are
 * set equal to the **perms** field of capability register *cs1*.
 * The other bits of *rd* are set to zero.
 */
function clause execute (CGetPerm(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = zero_extend(getCapPerms(capVal));
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **base** field of capability
 * register *cs1*.
 */
function clause execute (CGetBase(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = getCapBaseBits(capVal);
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **top** field of capability
 * register *cs1*.
 *
 * ## Notes
 *
 * - Due to the compressed representation of capabilities, the actual top
 *   of capabilities can be $2^{[{xlen}][xlen]}$; [CGetTop] will return the
 *   maximum value of $2^{[{xlen}][xlen]}-1$ in this case.
 */
function clause execute (CGetBound(rd, cs1)) = {
  let capVal = C(cs1);
  let top = getCapTop(capVal);
  X(rd) = to_bits(sizeof(xlen), if top > cap_max_addr then cap_max_addr else top);
  RETIRE_SUCCESS
}

/*!
 * Integer register *rd* is set equal to the **address** field of capability
 * register *cs1*.
 */
function clause execute (CGetAddr(rd, cs1)) = {
  let capVal = C(cs1);
  X(rd) = capVal.address;
  RETIRE_SUCCESS
}

union clause ast = CAndPerm : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of capability
 * register *cs1* with the **perms** field set to the bitwise AND of its
 * previous value and bits 0 to [cap_perms_width]-1 of integer register *rs2*.
 * If the resulting set of permissions cannot be represented by the capability
 * encoding then the result will have a (possibly empty) subset of the ANDed
 * permissions. If *cs1* was sealed and *rs2* codes for clearing anything other
 * than Permit_Global, then *cd*.**tag** is cleared.
 */
function clause execute(CAndPerm(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let perms = getCapPerms(cs1_val);
  let mask = truncate(rs2_val, cap_perms_width);

  let newperms = perms & mask;

  /*
   * CAndPerm on a sealed cap clears the tag unless the mask is all ones or
   * has *only* the global permission clear.
   *
   * Here, perm_global is a bit vector (in the architectural format used by
   * [CAndPerm] and [CGetPerm]) of all zeros except for the global permission
   * bit.  Its formulation here relies on null_cap having no asserted
   * permissions (which we verify in our SMT properties; see
   * [prop_null_noperms]).
   */
  let perm_global = getCapPerms({ null_cap with global = true });
  let inCap = clearTagIf(cs1_val,
                isCapSealed(cs1_val) & ((mask | perm_global) != ones()));

  let newCap = setCapPerms(inCap, newperms);

  C(cd) = newCap;
  RETIRE_SUCCESS
}

union clause ast = CSub : (regidx, regidx, regidx)
/*!
 * Integer register *rd* is set equal to (*cs1*.**address** $-$
 * *cs2*.**address**) $\bmod~2^{[{xlen}][xlen]}$.
 */
function clause execute(CSub(rd, cs1, cs2)) = {
  let cs2_val = C(cs2);
  let cs1_val = C(cs1);

  X(rd) = cs1_val.address - cs2_val.address;
  RETIRE_SUCCESS
}

union clause ast = CIncAddr : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *cs1*.**address** $+$ *rs2*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *cs1*.**address** $+$ *rs2* decodes to.
 */
function clause execute (CIncAddr(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let inCap = clearTagIfSealed(cs1_val);
  let (success, newCap) = incCapAddr(inCap, rs2_val);

  C(cd) = clearTagIf(newCap, not(success));
  RETIRE_SUCCESS
}

union clause ast = CIncAddrImmediate : (regidx, regidx, bits(12))
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *cs1*.**address** $+$ *imm*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *cs1*.**address** $+$ *imm* decodes to.
 */
function clause execute (CIncAddrImmediate(cd, cs1, imm)) = {
  let cs1_val = C(cs1);
  let immBits : xlenbits = sign_extend(imm);

  let inCap = clearTagIfSealed(cs1_val);
  let (success, newCap) = incCapAddr(inCap, immBits);

  C(cd) = clearTagIf(newCap, not(success));
  RETIRE_SUCCESS
}

union clause ast = CSetAddr : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set equal to capability register *cs1* with its
 * **address** replaced with *rs2*.
 * If the resulting capability cannot be represented exactly, or if *cs1* was
 * sealed, then *cd*.**tag** is cleared. The remaining capability fields are
 * set to what the in-memory representation of *cs1* with the address set to
 * *rs2* decodes to.
 */
function clause execute (CSetAddr(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let inCap = clearTagIfSealed(cs1_val);
  let (representable, newCap) = setCapAddr(inCap, rs2_val);

  C(cd) = clearTagIf(newCap, not(representable));
  RETIRE_SUCCESS
}


union clause ast = CSetBounds : (regidx, regidx, regidx)
/*!
 * Capability register *cd* is set to capability register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with integer register *rs2*. If the resulting capability cannot be
 * represented exactly the **base** will be rounded down and the **length**
 * will be rounded up by the smallest amount needed to form a representable
 * capability covering the requested bounds. The **tag** field of the result
 * is cleared if the bounds of the result exceed the bounds of *cs1*, or if
 * *cs1* was sealed.
 *
 * ## Notes
 *
 *  - This Sail code actually does the bounds check on the *requested* bounds,
 *    not the bounds that result from [setCapBounds]. This is an important
 *    distinction because the resulting bounds may be larger than the requested
 *    bounds, which could potentially lead to non-monotonic behaviour.
 *    However, providing that [setCapBounds] always returns the most precise
 *    encodable bounds it is safe to do the check on the requested bounds because,
 *    in the worst case, it would return the existing bounds. This is desirable
 *    because in hardware the bounds checking can be performed in parallel with
 *    computing the new bounds.
 */
function clause execute (CSetBounds(cd, cs1, rs2)) = {
  let cs1_val = C(cs1);
  let rs2_val = X(rs2);

  let newBase = cs1_val.address;
  let newLen  = rs2_val;
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(newLen));

  let inCap = clearTagIfSealed(cs1_val);
  let (_, newCap) = setCapBounds(inCap, newBase, newLen);

  C(cd) = clearTagIf(newCap, not(inBounds)); /* ignore exact */
  RETIRE_SUCCESS
}

union clause ast = CSetBoundsImmediate : (regidx, regidx, bits(12))
/*!
 * Capability register *cd* is set to capability register *cs1* with its
 * **base** field replaced with *cs1*.**address** and its **length** field
 * replaced with *uimm*. If the resulting capability cannot be represented
 * exactly the **base** will be rounded down and the **length** will be rounded
 * up by the smallest amount needed to form a representable capability covering
 * the requested bounds. The **tag** field of the result is cleared if the
 * bounds of the result exceed the bounds of *cs1*, or if *cs1* was sealed.
 *
 * ## Notes
 *  - The same caveat regarding the order of the bounds check applies as for
 *    [CSetBounds].
 */
function clause execute (CSetBoundsImmediate(cd, cs1, uimm)) = {
  let cs1_val = C(cs1);

  let newBase = cs1_val.address;
  let newLen : CapAddrBits = zero_extend(uimm);
  let inBounds = inCapBounds(cs1_val, newBase, unsigned(newLen));

  let inCap = clearTagIfSealed(cs1_val);
  let (_, newCap) = setCapBounds(inCap, newBase, newLen);

  C(cd) = clearTagIf(newCap, not(inBounds)); /* ignore exact */
  RETIRE_SUCCESS
}

union clause ast = CMove : (regidx, regidx)
/*!
 * Capability register *cd* is replaced with the contents of *cs1*.
 */
function clause execute (CMove(cd, cs1)) = {
  C(cd) = C(cs1);
  RETIRE_SUCCESS
}

union clause ast = CSEQX : (regidx, regidx, regidx)
/*!
 * Integer register *rd* is set to 1 if the **tag** fields and in-memory
 * representations of capability registers *cs1* and *cs2* are identical,
 * including any reserved encoding bits, otherwise it is set to 0.
 */
function clause execute (CSEQX(rd, cs1, cs2)) = {
  let cs1_val = C(cs1);
  let cs2_val = C(cs2);
  X(rd) = zero_extend(bool_to_bits(cs1_val == cs2_val));
  RETIRE_SUCCESS
}

union clause ast = LoadCapImm : (regidx, regidx, bits(12))
/*!
 * Capability register *cd* is
 * replaced with the capability located in memory at *cs1*.**address** $+$
 * *imm*, and if *cs1*.**perms** does not grant **Permit_Load_Capability** then
 * *cd*.**tag** is cleared.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Load**.
 *   - *cs1*.**address** $+$ *imm* $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *imm* $+$ **CLEN** $/$ 8 $\gt$ *cs1*.**top**.
 *   - *cs1*.**address** $+$ *imm* is unaligned, regardless of whether the
 *     implementation supports unaligned data accesses.
 */
function clause execute LoadCapImm(cd, cs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let auth_val = C(cs1);
  let vaddrBits = auth_val.address + offset;
  if not(auth_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not (auth_val.permit_load) then {
    handle_cheri_reg_exception(CapEx_PermitLoadViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, cap_size)) then {
    handle_cheri_reg_exception(CapEx_BoundsViolation, cs1);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_Load_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Read(Cap)) {
    TR_Failure(E_Extension(_), _) => { internal_error(__FILE__, __LINE__,"unexpected cheri exception for cap load") },
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, ptw_info) => {
      let c = mem_read_cap(addr, false, false, false);
      match c {
        MemValue(v) => {
          var cr = v;
          if ptw_info.ptw_lc == PTW_LC_CLEAR  | not(auth_val.permit_load_store_cap) then {
            cr.tag = false;
          };
          if cr.tag & not(auth_val.permit_load_global) then {
            /* Without load-global authority, the loaded cap is always local */
            cr.global = false;
            if not(isCapSealed(cr)) then {
              /*
               * Loading an unsealed capability without load global authority
               * results in attenuation of the loaded capability's permission,
               * transitively weakening the view through said authority.
               *
               * But sealing stops this transitivity.  Even if the authority
               * lacks load global permission, a loaded sealed cap retains its
               * load global permission, as it requires separate unsealing
               * authority to exercise.
               */
              cr.permit_load_global = false;
            }
          };
          if cr.tag & not(auth_val.permit_load_mutable) & not(isCapSealed(cr)) then {
            /*
             * Loading an unsealed capability without load mutable authority
             * also results in attenuated permissions.  As above, sealing stops
             * transitivity, but also the loaded sealed capability retains its
             * store permission.
             */
            cr.permit_store = false;
            cr.permit_load_mutable = false;
          };
          /* Sealing capabilities are excluded from revocation */
          let isSealingCap = cr.permit_seal | cr.permit_unseal | cr.perm_user0;
          if (cr.tag & not(isSealingCap)) then {
            let base = getCapBaseBits(cr);
            let granule_addr = align_down(log2_revocation_granule_size, base);
            let revoked = mem_read_cap_revoked(granule_addr);
            cr.tag = cr.tag & not(revoked);
          };
          C(cd) = cr;
          RETIRE_SUCCESS
        },
        MemException(e) => {handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
      }
    }
  }
}

union clause ast = StoreCapImm : (regidx, regidx, bits(12))
/*!
 * The capability located in memory at *cs1*.**address** $+$ *imm* is
 * replaced with capability register *cs2*.
 *
 * The stored capability will have its tag forcibly cleared if *cs1*.**perms**
 * does not grant **Permit_Store_Local_Capability** and *cs2*.**perms** does not
 * grant **Global**.
 *
 * ## Exceptions
 *
 * An exception is raised if:
 *   - *cs1*.**tag** is not set.
 *   - *cs1* is sealed.
 *   - *cs1*.**perms** does not grant **Permit_Store**.
 *   - *cs1*.**perms** does not grant **Permit_Store_Capability** and
 *     *cs2*.**tag** is set.
 *   - *cs1*.**address** $+$ *imm* $\lt$ *cs1*.**base**.
 *   - *cs1*.**address** $+$ *imm* $+$ **CLEN** $/$ 8 $\gt$ *cs1*.**top**.
 */
function clause execute StoreCapImm(cs2, cs1, imm) = {
  let offset : xlenbits = sign_extend(imm);
  let auth_val = C(cs1);
  let vaddrBits = auth_val.address + offset;
  let cs2_val = C(cs2);
  if not(auth_val.tag) then {
    handle_cheri_reg_exception(CapEx_TagViolation, cs1);
    RETIRE_FAIL
  } else if isCapSealed(auth_val) then {
    handle_cheri_reg_exception(CapEx_SealViolation, cs1);
    RETIRE_FAIL
  } else if not (auth_val.permit_store) then {
    handle_cheri_reg_exception(CapEx_PermitStoreViolation, cs1);
    RETIRE_FAIL
  } else if not (auth_val.permit_load_store_cap) & cs2_val.tag then {
    handle_cheri_reg_exception(CapEx_PermitStoreCapViolation, cs1);
    RETIRE_FAIL
  } else if not(inCapBounds(auth_val, vaddrBits, cap_size)) then {
    handle_cheri_reg_exception(CapEx_BoundsViolation, cs1);
    RETIRE_FAIL
  } else if not(is_aligned_addr(vaddrBits, cap_size)) then {
    handle_mem_exception(vaddrBits, E_SAMO_Addr_Align());
    RETIRE_FAIL
  } else match translateAddr(vaddrBits, Write(if cs2_val.tag then Cap else Data)) {
    TR_Failure(e, _) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
    TR_Address(addr, _) => {
      let eares : MemoryOpResult(unit) = mem_write_ea_cap(addr, false, false, false);
      match (eares) {
        MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL },
        MemValue(_) => {
          let stored_val =
              clearTagIf(cs2_val, not (auth_val.permit_store_local_cap) & not (cs2_val.global));
          let res : MemoryOpResult(bool) = mem_write_cap(addr, stored_val, false, false, false);
          match (res) {
            MemValue(true)  => RETIRE_SUCCESS,
            MemValue(false) => internal_error(__FILE__, __LINE__,"store got false from mem_write_value"),
            MemException(e) => { handle_mem_exception(vaddrBits, e); RETIRE_FAIL }
          }
        }
      }
    }
  }
}

/* Two arg */

mapping clause encdec = CGetPerm(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b00000 @ cs1 @ 0b011 @ rd @ 0b0001111 if (haveXcheri())
mapping clause encdec = CGetBase(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b00010 @ cs1 @ 0b011 @ rd @ 0b0001111 if (haveXcheri())
mapping clause encdec = CGetAddr(rd, cs1)   if (haveXcheri()) <-> 0b1111111 @ 0b01111 @ cs1 @ 0b011 @ rd @ 00001111 if (haveXcheri())
mapping clause encdec = CGetBound(rd, cs1)    if (haveXcheri()) <-> 0b1111111 @ 0b11000 @ cs1 @ 0b011 @ rd @ 0b0001111 if (haveXcheri())

mapping clause encdec = CMove(cd, cs1)      if (haveXcheri()) <-> 0b1111111 @ 0b01010 @ cs1 @ 0b011 @ cd @ 0b0001111 if (haveXcheri())

mapping clause assembly = CGetPerm(rd, cs1)   <-> "cgetperm"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetBase(rd, cs1)   <-> "cgetbase"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetAddr(rd, cs1)   <-> "cgetaddr"   ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)
mapping clause assembly = CGetBound(rd, cs1)    <-> "cgetbound"    ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1)

mapping clause assembly = CMove(cd, cs1)         <-> "cmove"      ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1)

/* Three arg */

mapping clause encdec = CAndPerm(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0001101 @ rs2 @ cs1 @ 0b011 @ cd @ 0b0001111 if (haveXcheri())
mapping clause encdec = CSetAddr(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010000 @ rs2 @ cs1 @ 0b011 @ cd @ 0b0001111 if (haveXcheri())
mapping clause encdec = CIncAddr(cd, cs1, rs2)    if (haveXcheri()) <-> 0b0010001 @ rs2 @ cs1 @ 0b011 @ cd @ 0b0001111 if (haveXcheri())
mapping clause encdec = CSetBounds(cd, cs1, rs2)  if (haveXcheri()) <-> 0b0001000 @ rs2 @ cs1 @ 0b011 @ cd @ 0b0001111 if (haveXcheri())

mapping clause encdec = CSub(rd, cs1, cs2)        if (haveXcheri()) <-> 0b0010100 @ cs2 @ cs1 @ 0b011 @ rd @ 0b0001111 if (haveXcheri())

mapping clause encdec = CIncAddrImmediate(cd, cs1, imm12) if (haveXcheri()) <-> imm12 : bits(12) @ cs1 @ 0b101 @ cd @ 0b0001111 if (haveXcheri())
mapping clause encdec = CSetBoundsImmediate(cd, cs1, imm12) if (haveXcheri()) <-> imm12 : bits(12) @ cs1 @ 0b110 @ cd @ 0b0001111 if (haveXcheri())

mapping clause encdec = CSEQX(rd, cs1, cs2) if (haveXcheri()) <-> 0b0100001 @ cs2 @ cs1 @ 0b011 @ rd @ 0b0001111 if (haveXcheri())

mapping clause assembly = CAndPerm(cd, cs1, rs2)   <-> "candperm"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetAddr(cd, cs1, rs2)   <-> "csetaddr"   ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CIncAddr(cd, cs1, rs2)   <-> "cincaddr" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)
mapping clause assembly = CSetBounds(cd, cs1, rs2) <-> "csetbounds" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ reg_name(rs2)

mapping clause assembly = CSub(rd, cs1, cs2)      <-> "csub"        ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)


mapping clause assembly = CIncAddrImmediate(cd, cs1, imm12)   <-> "cincaddrimm" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm12)
mapping clause assembly = CSetBoundsImmediate(cd, cs1, imm12) <-> "csetboundsimm" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ hex_bits_12(imm12)

mapping clause assembly = CSEQX(rd, cs1, cs2) <-> "cseqx" ^ spc() ^ reg_name(rd) ^ sep() ^ cap_reg_name(cs1) ^ sep() ^ cap_reg_name(cs2)

/* Loads and stores */

mapping clause encdec = LoadCapImm(cd, rs1, offset) <-> offset @ rs1 @ 0b111 @ cd @ 0b0000011 /* lc */
mapping clause encdec = StoreCapImm(cs2, rs1, off7 @ off5) <-> off7 : bits(7) @ cs2 @ rs1 @ 0b111 @ off5 : bits(5) @ 0b0100011 /* sc */

mapping clause assembly = LoadCapImm(cd, rs1, offset)   <-> "lc" ^ spc() ^ cap_reg_name(cd) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"
mapping clause assembly = StoreCapImm(cs2, rs1, offset) <-> "sc" ^ spc() ^ cap_reg_name(cs2) ^ sep() ^ hex_bits_12(offset) ^ opt_spc() ^ "(" ^ opt_spc() ^ reg_name(rs1) ^ opt_spc() ^ ")"


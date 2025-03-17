/*=======================================================================================*/
/*  Truisa RISCV Sail Model                                                              */
/*                                                                                       */
/*  Copyright (c) 2017-2025                                                              */
/*    Dong Tong, Peking University                                                       */
/*=======================================================================================*/

/* width of capability in bytes (excluding tag) */
type cap_size : Int = 8
let  cap_size = sizeof(cap_size)
type log2_cap_size : Int = 3
let  log2_cap_size = sizeof(log2_cap_size)
type CapBits = bits(8 * cap_size)

/*! Width of expanded exponent field in bits */
type cap_E_width : Int = 5
let  cap_E_width = sizeof(cap_E_width)
type cap_addr_width : Int = 24
let  cap_addr_width = sizeof(cap_addr_width)
/*! Cap length width is one larger than address space width in order to 
 represent maximum top / length of 2**cap_addr_width. */
type cap_len_width : Int = cap_addr_width + 1
let  cap_len_width = sizeof(cap_len_width)
/*! Width of the architectural perms returned by CGetPerms. */
type cap_perms_width : Int = 1
let  cap_perms_width = sizeof(cap_perms_width)

/*! THIS represents capabilities as stored in memory. */
struct EncCapability = {
  reserved32 : bits(32), /* don't need for 32-bit tagged pointer */
  mode       : bits(1)
  perms      : bits(cap_perms_width),
  reserved   : bits(1)
  E          : bits(cap_E_width),
  address    : bits(cap_addr_width)
}

function capBitsToEncCapability(c) : CapBits -> EncCapability = struct {
  reserved32 = c[63..32], /* don't need for 32-bit tagged pointer */
  mode       = c[31],
  perms      = c[30],
  reserved   = c[29],
  E          = c[28..24],
  address    = c[23..0]
}

function encCapToBits(cap) : EncCapability -> CapBits =
  cap.reserved32 @ /* don't need for 32-bit tagged pointer */
  cap.mode @
  cap.perms @
  cap.reserved @
  cap.E @
  cap.address

let cap_max_addr = MAX(cap_addr_width)

type CapAddrBits  = bits(cap_addr_width)
type CapAddrInt   = range(0, (2 ^ cap_addr_width) - 1)
type CapLenBits   = bits(cap_len_width)
type CapLen       = range(0, (2 ^ cap_len_width) - 1)
type CapPermsBits = bits(cap_perms_width)

/*! Exponent chosen to permit representing the entire address space. */
type cap_max_E : Int = 24
let cap_max_E = sizeof(cap_max_E)
let cap_max_E_bits = to_bits(cap_E_width, sizeof(cap_max_E))

/*!
 * THIS represents a partially decompressed capability. The
 * permissions, and E are expanded from their compressed format by
 * [encCapabilityToCapability] and compressed by [capToEncCap].
 */
struct Capability = {
  tag                    : bool,
  mode                   : bits(1),  
  permit_store           : bool,
  reserved               : bits(1),
  E                      : bits(cap_E_width),
  address                : bits(cap_addr_width)
}

/* The null capability is defined as all zeros, with tag unset. */
let null_cap : Capability = struct {
  tag                    = false,
  mode                   = zeros(),  
  permit_store           = false,
  reserved               = zeros(),
  E                      = zeros(),
  address                = zeros()
}

/* A capability from which to derive the root caps. E is set such that 
  the bounds decode to the entire address space, and tag is set.
  These things are are common to all root caps. For convenience it is derived 
  from null_cap. */
let max_bounds_cap : Capability = {
  null_cap with
  E                      = cap_max_E_bits,
  tag                    = true
}

/* The capability root for executable format capabilities. */
let root_cap_exe : Capability = max_bounds_cap

/* The capability root for memory format capabilities. */
let root_cap_mem : Capability = {
  max_bounds_cap with
  permit_store           = true
}

/*! Partially decompress a capability from bits to a [Capability] struct.
  Permissions and exponent are decompressed */
function encCapabilityToCapability(t,c) : (bool, EncCapability) -> Capability = {
  return struct {
    tag                    = t,
    permit_store           = c.perms,
    reserved               = c.reserved,
    E                      = c.E,
    address                = c.address
  }
}

function capBitsToCapability(t, c) : (bool, CapBits) -> Capability = encCapabilityToCapability(t, capBitsToEncCapability(c))

/*!
 * Compress a [Capability] back to the bits representation. This is simply
 * the reverse of [encCapabilityToCapability], although it relies on the fields
 * having valid values. In particular E must be either cap_max_E or less than 24,
 * Both of these will be true for things returned by [encCapabilityToCapability].
 * [CSetBounds] ensures a sensible value for E and nothing else sets it.
 */
function capToEncCap(cap) : Capability -> EncCapability = {
  return struct {
    reserved32 = zeros(32),
    mode = cap.mode,
    perms = cap.permit_store,
    reserved = cap.reserved,
    E = cap.E,
    address = cap.address
  };
}

/*! Convert from capability struct to bits (no tag) */
function capToBits(cap) : Capability -> CapBits = encCapToBits(capToEncCap(cap))

let null_cap_bits : CapBits = capToBits(null_cap)

/*!
 * Returns the decoded base and top of the given Capability.
 */

/*! In Truisa, all B-Type capability length is 2^E.
 * The base is the first address, and the bound is the last byte address. 
 */

/* TODO: Add S-Type Bounds if mode == 0b0 from a descriptor inside DLB.
*/
function getCapBoundsBits(c) : Capability -> (CapAddrBits, CapLenBits) =
  let E = min(cap_max_E, unsigned(c.E)) in
  let a : CapAddrBits = c.address in
  let a_top = (a >> E) in {
    base : CapAddrBits = truncate( 0b0 @ a_top       @ zeros(E), cap_addr_width);
    top  : CapLenBits = truncate(((0b0 @ a_top) + 1) @ zeros(E), cap_len_width);
  
  (base, top) 
  }

function getCapBounds(cap) : Capability -> (CapAddrInt, CapLen) =
  let (base : CapAddrBits, top : CapLenBits) = getCapBoundsBits(cap) in
  (unsigned(base), unsigned(top))

/*!
 * Returns cap with E set such that the decoded bounds include the
 * region specified by base and length. Also returns a
 * boolean indicating whether the bounds are precisely representable, and sets
 * the address of the returned capability to the requested base.
 */
function setCapBounds(cap, base, lenght) : (Capability, CapAddrBits, CapAddrnBits) -> (bool, Capability) = {
  let ext_length = 0b0 @ lenght;
  let e = cap_max_E - count_leading_zeros(length);

  let newCap = {cap with address = base, E = to_bits(cap_E_width, e)};
  let exact = true;
  (exact, newCap)
}

/* XXX this should go in prelude.sail but putting here for now to avoid submodule faff */
val count_trailing_zeros : forall 'N, 'N >=0 . bits('N) -> range(0, 'N)
function count_trailing_zeros(bv) = {
  foreach(i from 0 to ('N - 1) by 1 in inc) {
    if bv[i] == bitone then {
      return i;
    }
  };
  'N
}

function getCapPerms(cap) : Capability -> CapPermsBits = [
  bool_to_bit(cap.permit_store)
]

function setCapPerms(cap, perms) : (Capability, CapPermsBits) -> Capability = {
  cap with
  permit_store           = bit_to_bool(perms)
}

function getCapBaseBits(c) : Capability -> CapAddrBits =
    let (base, _) = getCapBoundsBits(c) in
    base

function getCapBase(c) : Capability -> CapAddrInt =
    unsigned(getCapBaseBits(c))

function getCapTopBits(c) : Capability -> CapLenBits =
    let (_, top) = getCapBoundsBits(c) in
    top

function getCapTop (c) : Capability -> CapLen =
    unsigned(getCapTopBits(c))

function getCapOffsetBits(c) : Capability -> CapAddrBits =
    let base : CapAddrBits = getCapBaseBits(c) in
    c.address - base

function getCapOffset(c) : Capability -> CapAddrInt =
    unsigned(getCapOffsetBits(c))

function getCapLength(c) : Capability -> CapLen =
    let ('base, 'top) = getCapBounds(c) in {
        /* For valid capabilties we expect top >= base and hence
         * length >= 0 but representation does allow top < base in some
         * cases so might encounter on untagged capabilities. Here we just
         * pretend it is a 65-bit quantitiy and wrap.
         */
        assert (not(c.tag) | top >= base);
        (top - base) % pow2(cap_len_width)
    }

/*!
 * THIS(cap, addr, len) checks whether the capability cap includes the region
 * specified by addr and len. Specifically it checks whether
 * cap.base $\le$ addr AND addr + len $\le$ cap.top. Note that this definition
 * returns true if len is zero and addr $=$ cap.top.
 */
val inCapBounds  : (Capability, CapAddrBits, CapLen) -> bool
function inCapBounds (cap, addr, size) = {
  let (base, top) = getCapBounds(cap);
  let a = unsigned(addr);
  (a >= base) & ((a + size) <= top)
}

function int_to_cap (offset) : CapAddrBits -> Capability =
    {null_cap with address = offset}

/*!
 * Returns the given capability with the tag cleared if the second argument is
 * true, otherwise returns it with the original tag value preserved.
 */
val clearTagIf : (Capability, bool) -> Capability
function clearTagIf(cap, cond) =
    {cap with tag = cap.tag & not(cond)}

/*!
 * Returns the given capability with the tag set to false.
 */
val clearTag : Capability -> Capability
function clearTag(cap) : Capability -> Capability =
    clearTagIf(cap, true)

function capBoundsEqual (c1, c2) : (Capability, Capability) -> bool =
    let (base1, top1) = getCapBounds(c1) in
    let (base2, top2) = getCapBounds(c2) in
    (base1 == base2) & (top1 == top2)

/*!
 * Returns the given capability with the address set to the given value and a boolean
 * indicating whether the new address is within representable range (decoded
 * bounds remain the same).
 */
val setCapAddr : (Capability, CapAddrBits) -> (bool, Capability)
function setCapAddr(c, addr) =
    let newCap = { c with address = addr } in
    let representable = capBoundsEqual(c, newCap) in
    (representable, newCap)

/*!
 * Returns the given capability with the address set to given value. If the new
 * address is not in the representable range or the capability is sealed then
 * the tag is cleared.
 */
val setCapAddrChecked : (Capability, CapAddrBits) -> Capability
function setCapAddrChecked (cap, addr) =
    let (representable, newCap) = setCapAddr(cap, addr) in
    clearTagIf(newCap, not(representable) | isCapSealed(cap))

infix 1 >>_s
overload operator >> = {sail_shiftright}
overload operator << = {sail_shiftleft}
overload operator >>_s = {sail_arith_shiftright}

function setCapOffset(c, offset) : (Capability, CapAddrBits) -> (bool, Capability) =
    let base = getCapBaseBits(c) in
    let newAddress = base + offset in
    let newCap     = { c with address = newAddress } in
    let representable = capBoundsEqual(c, newCap) in
    (representable, newCap)

function setCapOffsetChecked (cap, offset) : (Capability, CapAddrBits) -> Capability =
    let (representable, newCap) = setCapOffset(cap, offset) in
    clearTagIf(newCap, not(representable) | isCapSealed(cap))

/*!
 * Returns the given capability with the address incremented by the given value 
 * and a boolean indicating whether the new address is within representable 
 * range (decoded bounds remain the same).
 */
val incCapAddr : (Capability, CapAddrBits) -> (bool, Capability)
function incCapAddr(c, delta) =
    let newAddress : CapAddrBits = c.address + delta in
    let newCap     = { c with address = newAddress } in
    let representable = capBoundsEqual(c, newCap) in
    /* let representable = fastRepCheck(c, delta) in */
    (representable, newCap)


val capToString : (Capability) -> string
function capToString (cap) = {
  let len = getCapLength(cap);
  let len_str = BitStr(to_bits(cap_len_width + 3, len));
  let (base, top) = getCapBoundsBits(cap);
  let top_str = BitStr(0b000 @ top);
  BitStr(cap.address)
    ^ " (v:" ^ (if cap.tag then "1 " else "0 ")
    ^ BitStr(base) ^ "-" ^ top_str
    ^ " l:" ^ len_str
    ^ " o:" ^ BitStr(cap.otype)
    ^ " p:"
    ^ (if cap.permit_store then "W" else "-")
    /* ^ (if cap.permit_execute then "X" else "-") */
    ^ ")"
}

/*!
 * For a given length computes the exponent, $e$, that would be used to represent
 * a capability of that length and returns a mask consisting of $e$ zeros in the
 * least significant bits and ones in the upper bits.
 */
val getRepresentableAlignmentMask: xlenbits -> xlenbits
/*!
 * The representable alignment mask for a given length depends on the exponent
 * that would be used to represent a region of that length, assuming the base
 * is sufficiently aligned. To compute this we resuse the implementation of
 * [setCapBounds]
 */
function getRepresentableAlignmentMask(len) = {
  let (exact, c) = setCapBounds(root_cap_mem, to_bits(sizeof(xlen), 0), len);
  var e = unsigned(c.E);
  ones(sizeof(xlen)) << e
}

/*!
 * For a given length, $l$, returns a value greater than or equal to $l$ that
 * will result in a precisely representable capability when used with a
 * base that is suitably aligned as per [getRepresentableAlignmentMask].
 */
val getRepresentableLength : xlenbits -> xlenbits
/*!
 * Given the required alignment mask returned by [getRepresentableAlignmentMask]
 * we can round up the length by bit twiddling.
 */
function getRepresentableLength(len) = {
  let m = getRepresentableAlignmentMask(len);
  (len + ~(m)) & m
}

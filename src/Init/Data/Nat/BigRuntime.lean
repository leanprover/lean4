/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.Data.Nat.Big
public import Init.Data.SInt.Basic

/-!
# The runtime's big number primitives

A `Nat` larger than `LEAN_MAX_SMALL_NAT` is represented as a `ByteArray` holding its magnitude (see
`Init.Data.Nat.Big`). A big `Int` uses the same representation, followed by one byte `1` if it is
negative; a non-negative big `Int` is thus also a valid big `Nat` if it is large enough. As the digit
count of a magnitude is its byte size divided by four, the sign byte is invisible to the magnitude
functions.

The definitions in this module are exported as `lean_bignum_*` and wrapped by the runtime primitives
declared in `lean.h`, which borrow their arguments where these functions take ownership. As they are
called while `Init.Prelude` is being initialized, they must not refer to any module-level
constants.
-/

namespace Nat.Big.Runtime
open Nat.Big

/-! ## Object access -/

@[extern "lean_is_scalar"] public opaque isScalar (n : @& Nat) : Bool
@[extern "lean_unbox"] public opaque unbox (n : @& Nat) : USize
@[extern "lean_box"] public opaque box (n : USize) : Nat
@[extern "lean_is_scalar"] public opaque isScalarInt (n : @& Int) : Bool
@[extern "lean_unbox"] public opaque unboxInt (n : @& Int) : USize
/-- Must only be applied to values in the small `Int` range. -/
@[extern "lean_int64_to_int_sint"] public opaque ofSmallInt64 (n : Int64) : Int
@[extern "lean_internal_panic_string"] public opaque internalPanic (msg : @& String) : Nat

@[inline] public def is64 : Bool := ((0 : USize) - 1).toUInt64 == 0xFFFFFFFFFFFFFFFF

/-- The value of a scalar `Int`, as `lean_scalar_to_int64`: the low 32 (64-bit platforms) or
31 (32-bit platforms) bits of the unboxed value, sign-extended. -/
@[inline] public def scalarToInt64 (n : @& Int) : Int64 :=
  let v := (unboxInt n).toUInt32
  let v := if is64 || v &&& 0x40000000 == 0 then v else v ||| 0x80000000
  v.toInt32.toInt64
@[inline] public def maxSmallNat : USize := ((0 : USize) - 1) >>> 1
/-- `LEAN_MAX_SMALL_INT + 1`; the small `Int`s are `[-smallIntBound, smallIntBound)`. -/
@[inline] public def smallIntBound : UInt64 := if is64 then 0x80000000 else 0x40000000
@[inline] public def uintMax : USize := 0xFFFFFFFF

/-- The magnitude `1`, as a function so that it is not a module-level constant. -/
@[inline] public def one (_ : Unit) : Mag := ofUInt64 1

/-- The magnitude of a `Nat`. -/
@[inline] public unsafe def mag (n : @& Nat) : Mag :=
  if isScalar n then ofUInt64 (unbox n).toUInt64 else unsafeCast n

/-- The `Nat` with the normalized magnitude `m`. -/
@[inline] public unsafe def ofMag (m : Mag) : Nat :=
  if m.usize ≤ 2 then
    let v := low64 m
    if v ≤ maxSmallNat.toUInt64 then box v.toUSize else unsafeCast m
  else unsafeCast m

/-- Whether the big `Int` `b` is negative. -/
@[inline] public def isNegBig (b : @& ByteArray) : Bool := b.usize &&& 3 == 1

/-- Whether an `Int` is negative, and its magnitude. -/
@[inline] public unsafe def intMag (i : @& Int) : Bool × Mag :=
  if isScalarInt i then
    let v := scalarToInt64 i
    if v < 0 then (true, ofUInt64 (0 - v.toUInt64)) else (false, ofUInt64 v.toUInt64)
  else
    (isNegBig (unsafeCast i), unsafeCast i)

/-- The `Int` with sign `neg` and the normalized magnitude `m`, which may end in a sign byte. -/
public unsafe def ofIntMag (neg : Bool) (m : Mag) : Int :=
  let n := m.usize
  let v := low64 m
  if n ≤ 2 && (if neg then v ≤ smallIntBound else v < smallIntBound) then
    ofSmallInt64 (if neg then (0 - v).toInt64 else v.toInt64)
  else
    let m := if m.bytes.usize &&& 3 == 0 then m.bytes else m.bytes.shrink (n <<< 2).toNat
    if neg then unsafeCast (m.push 1) else unsafeCast m

/-! ## Construction -/

@[export lean_bignum_big_usize_to_nat]
public unsafe def bigUSizeToNat (n : USize) : Nat :=
  if n ≤ maxSmallNat then box n else unsafeCast (ofUInt64 n.toUInt64)

@[export lean_bignum_big_uint64_to_nat]
public unsafe def bigUInt64ToNat (n : UInt64) : Nat :=
  if n ≤ maxSmallNat.toUInt64 then box n.toUSize else unsafeCast (ofUInt64 n)

/-- Used by `lean_cstr_to_nat`. -/
@[export lean_bignum_nat_of_decimal]
public unsafe def natOfDecimal (s : String) : Nat := ofMag (ofDecimal s)

/-- Used by `lean_cstr_to_int`. -/
@[export lean_bignum_int_of_decimal]
public unsafe def intOfDecimal (s : String) : Int :=
  ofIntMag (s.toUTF8.get! 0 == '-'.toUInt8) (ofDecimal s)

@[export lean_bignum_nat_big_to_decimal]
public unsafe def natToDecimal (n : Nat) : String := toDecimal (mag n)

@[export lean_bignum_big_size_t_to_int]
public unsafe def bigSizeTToInt (n : USize) : Int := ofIntMag false (ofUInt64 n.toUInt64)

@[export lean_bignum_big_int64_to_int]
public unsafe def bigInt64ToInt (n : Int64) : Int :=
  if n < 0 then ofIntMag true (ofUInt64 (0 - n.toUInt64)) else ofIntMag false (ofUInt64 n.toUInt64)

@[export lean_bignum_big_int_to_int]
public unsafe def bigIntToInt (n : Int32) : Int := bigInt64ToInt n.toInt64

/-! ## `Nat` arithmetic -/

@[export lean_bignum_nat_big_succ]
public unsafe def natSucc (a : Nat) : Nat := ofMag (add (mag a) (one ()))

@[export lean_bignum_nat_big_add]
public unsafe def natAdd (a b : Nat) : Nat := ofMag (add (mag a) (mag b))

@[export lean_bignum_nat_big_sub]
public unsafe def natSub (a b : Nat) : Nat :=
  let ma := mag a
  let mb := mag b
  if cmp ma mb == .lt then box 0 else ofMag (sub ma mb)

@[export lean_bignum_nat_big_mul]
public unsafe def natMul (a b : Nat) : Nat := ofMag (mul (mag a) (mag b))

@[export lean_bignum_nat_overflow_mul]
public unsafe def natOverflowMul (a b : USize) : Nat :=
  ofMag (mul (ofUInt64 a.toUInt64) (ofUInt64 b.toUInt64))

@[inline] public def isZero (n : @& Nat) : Bool := isScalar n && unbox n == 0

@[export lean_bignum_nat_big_div]
public unsafe def natDiv (a b : Nat) : Nat :=
  if isZero b then box 0 else ofMag (divMod (mag a) (mag b)).1

@[export lean_bignum_nat_big_div_exact]
public unsafe def natDivExact (a b : Nat) : Nat := natDiv a b

@[export lean_bignum_nat_big_mod]
public unsafe def natMod (a b : Nat) : Nat :=
  if isZero b then a else ofMag (divMod (mag a) (mag b)).2

@[export lean_bignum_nat_big_eq]
public unsafe def natEq (a b : Nat) : Bool := cmp (mag a) (mag b) == .eq

@[export lean_bignum_nat_big_le]
public unsafe def natLe (a b : Nat) : Bool := cmp (mag a) (mag b) != .gt

@[export lean_bignum_nat_big_lt]
public unsafe def natLt (a b : Nat) : Bool := cmp (mag a) (mag b) == .lt

@[export lean_bignum_nat_big_land]
public unsafe def natLand (a b : Nat) : Nat := ofMag (land (mag a) (mag b))

@[export lean_bignum_nat_big_lor]
public unsafe def natLor (a b : Nat) : Nat := ofMag (lor (mag a) (mag b))

@[export lean_bignum_nat_big_xor]
public unsafe def natXor (a b : Nat) : Nat := ofMag (xor (mag a) (mag b))

@[export lean_bignum_nat_shiftl]
public unsafe def natShiftLeft (a b : Nat) : Nat :=
  if isZero a then box 0
  else if !isScalar b || unbox b > uintMax then internalPanic "Nat.shiftl exponent is too big"
  else ofMag (shiftLeft (mag a) (unbox b))

@[export lean_bignum_nat_big_shiftr]
public unsafe def natShiftRight (a b : Nat) : Nat :=
  if !isScalar b then box 0 else
    let s := unbox b
    let ma := mag a
    if s > uintMax then
      if ma.usize != 0 && log2 ma ≥ s then internalPanic "Nat.shiftr exponent is too big" else box 0
    else ofMag (shiftRight ma s)

@[export lean_bignum_nat_pow]
public unsafe def natPow (a b : Nat) : Nat :=
  if !isScalar b || unbox b > uintMax then
    -- The result would exhaust memory for any base `≥ 2`.
    if isScalar a && unbox a ≤ 1 then a else internalPanic "Nat.pow exponent is too big"
  else ofMag (pow (mag a) (unbox b))

@[export lean_bignum_nat_powmod]
public unsafe def natPowMod (b e m : Nat) : Nat :=
  if isZero m then natPow b e
  else if isScalar m && unbox m == 1 then box 0
  else ofMag (powMod (mag b) (mag e) (mag m))

public unsafe def gcdUSize (a b : USize) : USize := if b == 0 then a else gcdUSize b (a % b)

@[export lean_bignum_nat_gcd]
public unsafe def natGcd (a b : Nat) : Nat :=
  if isScalar a && isScalar b then box (gcdUSize (unbox a) (unbox b))
  else ofMag (gcd (mag a) (mag b))

public def log2USize (n : USize) : USize := (n.toUInt64.log2).toUSize

@[export lean_bignum_nat_log2]
public unsafe def natLog2 (a : Nat) : Nat :=
  if isScalar a then box (log2USize (unbox a)) else box (log2 (mag a))

/-- The size of `a`'s representation in bytes; used for the kernel's size limits. -/
@[export lean_bignum_nat_size_in_bytes]
public unsafe def natSizeInBytes (a : Nat) : USize :=
  if isScalar a then (if is64 then 8 else 4) else (mag a).bytes.usize

@[inline] public unsafe def trailingZerosUSize (n : USize) : USize :=
  if n == 0 then 0 else trailingZeros (ofUInt64 n.toUInt64)

@[export lean_bignum_nat_trailing_zeros]
public unsafe def natTrailingZeros (a : Nat) : Nat :=
  if isScalar a then box (trailingZerosUSize (unbox a)) else box (trailingZeros (mag a))

@[export lean_bignum_int_trailing_zeros]
public unsafe def intTrailingZeros (a : Int) : Nat :=
  -- the magnitude has the same trailing zeros as the two's complement representation
  let (_, m) := intMag a
  if m.usize == 0 then box 0 else box (trailingZeros m)

/-! ## `Int` arithmetic -/

@[export lean_bignum_big_int_to_nat]
public unsafe def bigIntToNat (a : Int) : Nat := ofMag (unsafeCast a)

@[export lean_bignum_int_big_neg]
public unsafe def intNeg (a : Int) : Int :=
  let (n, m) := intMag a
  ofIntMag (!n) m

@[inline] public unsafe def signedAdd (na : Bool) (ma : Mag) (nb : Bool) (mb : Mag) : Int :=
  if na == nb then ofIntMag na (add ma mb)
  else if cmp ma mb == .lt then ofIntMag nb (sub mb ma)
  else ofIntMag na (sub ma mb)

@[export lean_bignum_int_big_add]
public unsafe def intAdd (a b : Int) : Int :=
  let (na, ma) := intMag a
  let (nb, mb) := intMag b
  signedAdd na ma nb mb

@[export lean_bignum_int_big_sub]
public unsafe def intSub (a b : Int) : Int :=
  let (na, ma) := intMag a
  let (nb, mb) := intMag b
  signedAdd na ma (!nb) mb

@[export lean_bignum_int_big_mul]
public unsafe def intMul (a b : Int) : Int :=
  let (na, ma) := intMag a
  let (nb, mb) := intMag b
  ofIntMag (na != nb) (mul ma mb)

@[inline] public def isZeroInt (i : @& Int) : Bool := isScalarInt i && scalarToInt64 i == 0

/-- Division rounding toward zero. -/
@[export lean_bignum_int_big_div]
public unsafe def intDiv (a b : Int) : Int :=
  if isZeroInt b then b else
    let (na, ma) := intMag a
    let (nb, mb) := intMag b
    ofIntMag (na != nb) (divMod ma mb).1

@[export lean_bignum_int_big_div_exact]
public unsafe def intDivExact (a b : Int) : Int := intDiv a b

/-- The remainder of `intDiv`, which has the sign of `a`. -/
@[export lean_bignum_int_big_mod]
public unsafe def intMod (a b : Int) : Int :=
  if isZeroInt b then a else
    let (na, ma) := intMag a
    let (_, mb) := intMag b
    ofIntMag na (divMod ma mb).2

/-- Euclidean division: the remainder is non-negative. -/
@[export lean_bignum_int_big_ediv]
public unsafe def intEDiv (a b : Int) : Int :=
  if isZeroInt b then b else
    let (na, ma) := intMag a
    let (nb, mb) := intMag b
    let (q, r) := divMod ma mb
    if na && r.usize != 0 then ofIntMag (!nb) (add q (one ())) else ofIntMag (na != nb) q

@[export lean_bignum_int_big_emod]
public unsafe def intEMod (a b : Int) : Int :=
  if isZeroInt b then a else
    let (na, ma) := intMag a
    let (_, mb) := intMag b
    let r := (divMod ma mb).2
    if na && r.usize != 0 then ofIntMag false (sub mb r) else ofIntMag false r

@[inline] public unsafe def intCmp (a b : @& Int) : Ordering :=
  let (na, ma) := intMag a
  let (nb, mb) := intMag b
  if na != nb then (if na then .lt else .gt)
  else if na then cmp mb ma
  else cmp ma mb

@[export lean_bignum_int_big_eq]
public unsafe def intEq (a b : Int) : Bool := intCmp a b == .eq

@[export lean_bignum_int_big_le]
public unsafe def intLe (a b : Int) : Bool := intCmp a b != .gt

@[export lean_bignum_int_big_lt]
public unsafe def intLt (a b : Int) : Bool := intCmp a b == .lt

@[export lean_bignum_int_big_nonneg]
public unsafe def intNonneg (a : Int) : Bool := !(intMag a).1

/-! ## Conversions to fixed-width integers (modulo the width) -/

@[export lean_bignum_uint8_of_big_nat]
public unsafe def uint8OfBigNat (a : Nat) : UInt8 := (low64 (mag a)).toUInt8

@[export lean_bignum_uint16_of_big_nat]
public unsafe def uint16OfBigNat (a : Nat) : UInt16 := (low64 (mag a)).toUInt16

@[export lean_bignum_uint32_of_big_nat]
public unsafe def uint32OfBigNat (a : Nat) : UInt32 := (low64 (mag a)).toUInt32

@[export lean_bignum_uint64_of_big_nat]
public unsafe def uint64OfBigNat (a : Nat) : UInt64 := low64 (mag a)

@[export lean_bignum_usize_of_big_nat]
public unsafe def usizeOfBigNat (a : Nat) : USize := (low64 (mag a)).toUSize

/-- The two's complement bits of `a` modulo `2^64`. -/
@[inline] public unsafe def low64Int (a : @& Int) : UInt64 :=
  let (n, m) := intMag a
  if n then 0 - low64 m else low64 m

@[export lean_bignum_int8_of_big_int]
public unsafe def int8OfBigInt (a : Int) : Int8 := (low64Int a).toUInt8.toInt8

@[export lean_bignum_int16_of_big_int]
public unsafe def int16OfBigInt (a : Int) : Int16 := (low64Int a).toUInt16.toInt16

@[export lean_bignum_int32_of_big_int]
public unsafe def int32OfBigInt (a : Int) : Int32 := (low64Int a).toUInt32.toInt32

@[export lean_bignum_int64_of_big_int]
public unsafe def int64OfBigInt (a : Int) : Int64 := (low64Int a).toInt64

@[export lean_bignum_isize_of_big_int]
public unsafe def isizeOfBigInt (a : Int) : ISize := ISize.ofUSize (low64Int a).toUSize

end Nat.Big.Runtime

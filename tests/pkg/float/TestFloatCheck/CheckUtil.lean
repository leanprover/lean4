/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

/-!
Helpers shared by `TestFloatCheck`, which checks the model against the committed
TestFloat-format test vectors for both `binary32` and `binary64`.
-/

open Float.Model

public def hexToUInt64? (s : String) : Option UInt64 :=
  if s.isEmpty then none
  else s.foldl (init := some 0) fun acc c => do
    let acc ← acc
    let d ←
      if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none
    some (acc * 16 + UInt64.ofNat d)

/-- Render `x` as a zero-padded hexadecimal string of `width` digits. -/
private def toHexWidth (width : Nat) (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- Render a `binary64` bit pattern as 16 hexadecimal digits. -/
public def toHex (x : UInt64) : String := toHexWidth 16 x

/-- Render a `binary32` bit pattern (held in the low 32 bits) as 8 hexadecimal digits. -/
public def toHex32 (x : UInt64) : String := toHexWidth 8 x

/-- Whether a `binary64` bit pattern is a `NaN` (maximal exponent, nonzero mantissa). -/
public def isNaNBits (x : UInt64) : Bool :=
  (x >>> 52) &&& 0x7FF == 0x7FF && (x &&& 0x000FFFFFFFFFFFFF) != 0

/--
Whether a `binary32` bit pattern (held in the low 32 bits of `x`) is a `NaN`
(maximal 8-bit exponent, nonzero 23-bit mantissa).
-/
public def isNaNBits32 (x : UInt64) : Bool :=
  (x >>> 23) &&& 0xFF == 0xFF && (x &&& 0x7FFFFF) != 0

public def modelBinop (op : Float.Model → Float.Model → Float.Model)
    (a b : UInt64) : UInt64 :=
  (op (Float.Model.ofBits a) (Float.Model.ofBits b)).toBits

public def modelUnop (op : Float.Model → Float.Model)
    (a : UInt64) : UInt64 :=
  (op (Float.Model.ofBits a)).toBits

/--
Adapts a comparison on `Float.Model`s to operate on `binary64` bit patterns,
returning `1` for a true result and `0` for a false one to match the boolean
result column TestFloat emits for `f64_eq`, `f64_le`, and `f64_lt`.
-/
public def modelCompare (op : Float.Model → Float.Model → Bool) (a b : UInt64) : UInt64 :=
  if op (Float.Model.ofBits a) (Float.Model.ofBits b) then 1 else 0

/-- `binary32` counterpart of `modelBinop`; bit patterns are held in the low 32 bits. -/
public def modelBinop32 (op : Float32.Model → Float32.Model → Float32.Model)
    (a b : UInt64) : UInt64 :=
  (op (Float32.Model.ofBits a.toUInt32) (Float32.Model.ofBits b.toUInt32)).toBits.toUInt64

/-- `binary32` counterpart of `modelUnop`. -/
public def modelUnop32 (op : Float32.Model → Float32.Model)
    (a : UInt64) : UInt64 :=
  (op (Float32.Model.ofBits a.toUInt32)).toBits.toUInt64

/-- `binary32` counterpart of `modelCompare`. -/
public def modelCompare32 (op : Float32.Model → Float32.Model → Bool) (a b : UInt64) : UInt64 :=
  if op (Float32.Model.ofBits a.toUInt32) (Float32.Model.ofBits b.toUInt32) then 1 else 0

/--
Adapts a `binary64` operation on Lean's native `Float` to operate on bit
patterns, so the model can be checked against the hardware it models.
-/
public def nativeBinop (op : Float → Float → Float) (a b : UInt64) : UInt64 :=
  (op (Float.ofBits a) (Float.ofBits b)).toBits

/-- `Float` counterpart of `modelUnop`. -/
public def nativeUnop (op : Float → Float) (a : UInt64) : UInt64 :=
  (op (Float.ofBits a)).toBits

/-- `Float` counterpart of `modelCompare`. -/
public def nativeCompare (op : Float → Float → Bool) (a b : UInt64) : UInt64 :=
  if op (Float.ofBits a) (Float.ofBits b) then 1 else 0

/-- `Float32` counterpart of `nativeBinop`; bit patterns are held in the low 32 bits. -/
public def nativeBinop32 (op : Float32 → Float32 → Float32) (a b : UInt64) : UInt64 :=
  (op (Float32.ofBits a.toUInt32) (Float32.ofBits b.toUInt32)).toBits.toUInt64

/-- `Float32` counterpart of `nativeUnop`. -/
public def nativeUnop32 (op : Float32 → Float32) (a : UInt64) : UInt64 :=
  (op (Float32.ofBits a.toUInt32)).toBits.toUInt64

/-- `Float32` counterpart of `nativeCompare`. -/
public def nativeCompare32 (op : Float32 → Float32 → Bool) (a b : UInt64) : UInt64 :=
  if op (Float32.ofBits a.toUInt32) (Float32.ofBits b.toUInt32) then 1 else 0

/-!
Integer-to-float conversions. TestFloat emits these as unary vectors whose single
operand is an integer bit pattern (32- or 64-bit, held in the low bits of the
parsed `UInt64`) and whose expected result is a `binary32`/`binary64` bit pattern.
Signed 32-bit inputs are sign-extended by reinterpreting the low 32 bits via
`UInt32.toInt32`; signed 64-bit inputs via `UInt64.toInt64`.
-/

/-- `Float.Model` (`binary64`) conversion from a 32-bit unsigned operand. -/
public def modelOfUInt32 (a : UInt64) : UInt64 := (Float.Model.ofUInt32 a.toUInt32).toBits
/-- `Float.Model` (`binary64`) conversion from a 64-bit unsigned operand. -/
public def modelOfUInt64 (a : UInt64) : UInt64 := (Float.Model.ofUInt64 a).toBits
/-- `Float.Model` (`binary64`) conversion from a 32-bit signed operand. -/
public def modelOfInt32 (a : UInt64) : UInt64 := (Float.Model.ofInt32 a.toUInt32.toInt32).toBits
/-- `Float.Model` (`binary64`) conversion from a 64-bit signed operand. -/
public def modelOfInt64 (a : UInt64) : UInt64 := (Float.Model.ofInt64 a.toInt64).toBits

/-- `Float32.Model` (`binary32`) conversion from a 32-bit unsigned operand. -/
public def modelOfUInt32_32 (a : UInt64) : UInt64 := (Float32.Model.ofUInt32 a.toUInt32).toBits.toUInt64
/-- `Float32.Model` (`binary32`) conversion from a 64-bit unsigned operand. -/
public def modelOfUInt64_32 (a : UInt64) : UInt64 := (Float32.Model.ofUInt64 a).toBits.toUInt64
/-- `Float32.Model` (`binary32`) conversion from a 32-bit signed operand. -/
public def modelOfInt32_32 (a : UInt64) : UInt64 := (Float32.Model.ofInt32 a.toUInt32.toInt32).toBits.toUInt64
/-- `Float32.Model` (`binary32`) conversion from a 64-bit signed operand. -/
public def modelOfInt64_32 (a : UInt64) : UInt64 := (Float32.Model.ofInt64 a.toInt64).toBits.toUInt64

/-- Native `Float` (`binary64`) conversion from a 32-bit unsigned operand. -/
public def nativeOfUInt32 (a : UInt64) : UInt64 := a.toUInt32.toFloat.toBits
/-- Native `Float` (`binary64`) conversion from a 64-bit unsigned operand. -/
public def nativeOfUInt64 (a : UInt64) : UInt64 := a.toFloat.toBits
/-- Native `Float` (`binary64`) conversion from a 32-bit signed operand. -/
public def nativeOfInt32 (a : UInt64) : UInt64 := a.toUInt32.toInt32.toFloat.toBits
/-- Native `Float` (`binary64`) conversion from a 64-bit signed operand. -/
public def nativeOfInt64 (a : UInt64) : UInt64 := a.toInt64.toFloat.toBits

/-- Native `Float32` (`binary32`) conversion from a 32-bit unsigned operand. -/
public def nativeOfUInt32_32 (a : UInt64) : UInt64 := a.toUInt32.toFloat32.toBits.toUInt64
/-- Native `Float32` (`binary32`) conversion from a 64-bit unsigned operand. -/
public def nativeOfUInt64_32 (a : UInt64) : UInt64 := a.toFloat32.toBits.toUInt64
/-- Native `Float32` (`binary32`) conversion from a 32-bit signed operand. -/
public def nativeOfInt32_32 (a : UInt64) : UInt64 := a.toUInt32.toInt32.toFloat32.toBits.toUInt64
/-- Native `Float32` (`binary32`) conversion from a 64-bit signed operand. -/
public def nativeOfInt64_32 (a : UInt64) : UInt64 := a.toInt64.toFloat32.toBits.toUInt64

/-!
Float-to-integer conversions. TestFloat emits these as unary vectors whose single
operand is a `binary32`/`binary64` bit pattern and whose expected result is an
integer bit pattern (32- or 64-bit, held in the low bits of the parsed `UInt64`;
signed types are two's complement). The 32-bit results are rendered with 8 hex
digits and the 64-bit results with 16, and unlike the float results they are never
classified as `NaN`.
-/

/-- `Float.Model` (`binary64`) conversion to a 32-bit unsigned result. -/
public def modelToUInt32 (a : UInt64) : UInt64 := (Float.Model.ofBits a).toUInt32.toUInt64
/-- `Float.Model` (`binary64`) conversion to a 64-bit unsigned result. -/
public def modelToUInt64 (a : UInt64) : UInt64 := (Float.Model.ofBits a).toUInt64
/-- `Float.Model` (`binary64`) conversion to a 32-bit signed result. -/
public def modelToInt32 (a : UInt64) : UInt64 := (Float.Model.ofBits a).toInt32.toUInt32.toUInt64
/-- `Float.Model` (`binary64`) conversion to a 64-bit signed result. -/
public def modelToInt64 (a : UInt64) : UInt64 := (Float.Model.ofBits a).toInt64.toUInt64

/-- `Float32.Model` (`binary32`) conversion to a 32-bit unsigned result. -/
public def modelToUInt32_32 (a : UInt64) : UInt64 := (Float32.Model.ofBits a.toUInt32).toUInt32.toUInt64
/-- `Float32.Model` (`binary32`) conversion to a 64-bit unsigned result. -/
public def modelToUInt64_32 (a : UInt64) : UInt64 := (Float32.Model.ofBits a.toUInt32).toUInt64
/-- `Float32.Model` (`binary32`) conversion to a 32-bit signed result. -/
public def modelToInt32_32 (a : UInt64) : UInt64 := (Float32.Model.ofBits a.toUInt32).toInt32.toUInt32.toUInt64
/-- `Float32.Model` (`binary32`) conversion to a 64-bit signed result. -/
public def modelToInt64_32 (a : UInt64) : UInt64 := (Float32.Model.ofBits a.toUInt32).toInt64.toUInt64

/-- Native `Float` (`binary64`) conversion to a 32-bit unsigned result. -/
public def nativeToUInt32 (a : UInt64) : UInt64 := (Float.ofBits a).toUInt32.toUInt64
/-- Native `Float` (`binary64`) conversion to a 64-bit unsigned result. -/
public def nativeToUInt64 (a : UInt64) : UInt64 := (Float.ofBits a).toUInt64
/-- Native `Float` (`binary64`) conversion to a 32-bit signed result. -/
public def nativeToInt32 (a : UInt64) : UInt64 := (Float.ofBits a).toInt32.toUInt32.toUInt64
/-- Native `Float` (`binary64`) conversion to a 64-bit signed result. -/
public def nativeToInt64 (a : UInt64) : UInt64 := (Float.ofBits a).toInt64.toUInt64

/-- Native `Float32` (`binary32`) conversion to a 32-bit unsigned result. -/
public def nativeToUInt32_32 (a : UInt64) : UInt64 := (Float32.ofBits a.toUInt32).toUInt32.toUInt64
/-- Native `Float32` (`binary32`) conversion to a 64-bit unsigned result. -/
public def nativeToUInt64_32 (a : UInt64) : UInt64 := (Float32.ofBits a.toUInt32).toUInt64
/-- Native `Float32` (`binary32`) conversion to a 32-bit signed result. -/
public def nativeToInt32_32 (a : UInt64) : UInt64 := (Float32.ofBits a.toUInt32).toInt32.toUInt32.toUInt64
/-- Native `Float32` (`binary32`) conversion to a 64-bit signed result. -/
public def nativeToInt64_32 (a : UInt64) : UInt64 := (Float32.ofBits a.toUInt32).toInt64.toUInt64

public inductive Operation where
  /-- A binary operation on bit patterns. -/
  | binary (symbol : Char) (op : UInt64 → UInt64 → UInt64)
  /-- A unary operation on bit patterns. -/
  | unary (name : String) (op : UInt64 → UInt64)

/--
A checkable operation together with the precision-specific helpers needed to
compare and display its results: `isNaN` classifies a result as a `NaN` (so
`NaN`s are compared as a class rather than bit-for-bit), and `toHex` renders a
bit pattern for failure messages.
-/
public structure Check where
  /-- The operation under test, acting on bit patterns. -/
  op : Operation
  /-- Classifies a result bit pattern as a `NaN`. -/
  isNaN : UInt64 → Bool
  /-- Renders a bit pattern as hexadecimal for display. -/
  toHex : UInt64 → String

/-- A `binary64` operation paired with its `binary64` `NaN` test and hex renderer. -/
public def f64Check (op : Operation) : Check := { op, isNaN := isNaNBits, toHex := toHex }

/-- A `binary32` operation paired with its `binary32` `NaN` test and hex renderer. -/
public def f32Check (op : Operation) : Check := { op, isNaN := isNaNBits32, toHex := toHex32 }

/--
An operation producing a 32-bit integer result (e.g. a float-to-int conversion).
Integer results are compared bit-for-bit — never classified as `NaN` — and rendered
as 8 hexadecimal digits.
-/
public def i32Check (op : Operation) : Check := { op, isNaN := fun _ => false, toHex := toHex32 }

/--
An operation producing a 64-bit integer result. Like `i32Check` but rendered as
16 hexadecimal digits.
-/
public def i64Check (op : Operation) : Check := { op, isNaN := fun _ => false, toHex := toHex }

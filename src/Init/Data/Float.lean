/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Data.Int.Basic
import Init.Data.ToString.Basic

structure FloatSpec where
  float : Type
  val   : float
  lt    : float → float → Prop
  le    : float → float → Prop
  decLt : DecidableRel lt
  decLe : DecidableRel le

-- Just show FloatSpec is inhabited.
opaque floatSpec : FloatSpec := {
  float := Unit,
  val   := (),
  lt    := fun _ _ => True,
  le    := fun _ _ => True,
  decLt := fun _ _ => inferInstanceAs (Decidable True),
  decLe := fun _ _ => inferInstanceAs (Decidable True)
}

/--
64-bit floating-point numbers.

`Float` corresponds to the IEEE 754 *binary64* format (`double` in C or `f64` in Rust).
Floating-point numbers are a finite representation of a subset of the real numbers, extended with
extra “sentinel” values that represent undefined and infinite results as well as separate positive
and negative zeroes. Arithmetic on floating-point numbers approximates the corresponding operations
on the real numbers by rounding the results to numbers that are representable, propagating error and
infinite values.

Floating-point numbers include [subnormal numbers](https://en.wikipedia.org/wiki/Subnormal_number).
Their special values are:
 * `NaN`, which denotes a class of “not a number” values that result from operations such as
   dividing zero by zero, and
 * `Inf` and `-Inf`, which represent positive and infinities that result from dividing non-zero
   values by zero.
-/
structure Float where
  val : floatSpec.float

instance : Nonempty Float := ⟨{ val := floatSpec.val }⟩

/--
Adds two 64-bit floating-point numbers according to IEEE 754. Typically used via the `+` operator.

This function does not reduce in the kernel. It is compiled to the C addition operator.
-/
@[extern "lean_float_add"] opaque Float.add : Float → Float → Float
/--
Subtracts 64-bit floating-point numbers according to IEEE 754. Typically used via the `-` operator.

This function does not reduce in the kernel. It is compiled to the C subtraction operator.
-/
@[extern "lean_float_sub"] opaque Float.sub : Float → Float → Float
/--
Multiplies 64-bit floating-point numbers according to IEEE 754. Typically used via the `*` operator.

This function does not reduce in the kernel. It is compiled to the C multiplication operator.
-/
@[extern "lean_float_mul"] opaque Float.mul : Float → Float → Float
/--
Divides 64-bit floating-point numbers according to IEEE 754. Typically used via the `/` operator.

In Lean, division by zero typically yields zero. For `Float`, it instead yields either `Inf`,
`-Inf`, or `NaN`.

This function does not reduce in the kernel. It is compiled to the C division operator.
-/
@[extern "lean_float_div"] opaque Float.div : Float → Float → Float
/--
Negates 64-bit floating-point numbers according to IEEE 754. Typically used via the `-` prefix
operator.

This function does not reduce in the kernel. It is compiled to the C negation operator.
-/
@[extern "lean_float_negate"] opaque Float.neg : Float → Float

set_option bootstrap.genMatcherCode false
/--
Strict inequality of floating-point numbers. Typically used via the `<` operator.
-/
def Float.lt : Float → Float → Prop := fun a b =>
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.lt a b

/--
Non-strict inequality of floating-point numbers. Typically used via the `≤` operator.
-/
def Float.le : Float → Float → Prop := fun a b =>
  floatSpec.le a.val b.val

/--
Bit-for-bit conversion from `UInt64`. Interprets a `UInt64` as a `Float`, ignoring the numeric value
and treating the `UInt64`'s bit pattern as a `Float`.

`Float`s and `UInt64`s have the same endianness on all supported platforms. IEEE 754 very precisely
specifies the bit layout of floats.

This function does not reduce in the kernel.
-/
@[extern "lean_float_of_bits"] opaque Float.ofBits : UInt64 → Float

/--
Bit-for-bit conversion to `UInt64`. Interprets a `Float` as a `UInt64`, ignoring the numeric value
and treating the `Float`'s bit pattern as a `UInt64`.

`Float`s and `UInt64`s have the same endianness on all supported platforms. IEEE 754 very precisely
specifies the bit layout of floats.

This function is distinct from `Float.toUInt64`, which attempts to preserve the numeric value rather
than reinterpreting the bit pattern.
-/
@[extern "lean_float_to_bits"] opaque Float.toBits : Float → UInt64

instance : Add Float := ⟨Float.add⟩
instance : Sub Float := ⟨Float.sub⟩
instance : Mul Float := ⟨Float.mul⟩
instance : Div Float := ⟨Float.div⟩
instance : Neg Float := ⟨Float.neg⟩
instance : LT Float  := ⟨Float.lt⟩
instance : LE Float  := ⟨Float.le⟩

/--
Checks whether two floating-point numbers are equal according to IEEE 754.

Floating-point equality does not correspond with propositional equality. In particular, it is not
reflexive since `NaN != NaN`, and it is not a congruence because `0.0 == -0.0`, but
`1.0 / 0.0 != 1.0 / -0.0`.

This function does not reduce in the kernel. It is compiled to the C equality operator.
-/
@[extern "lean_float_beq"] opaque Float.beq (a b : Float) : Bool

instance : BEq Float := ⟨Float.beq⟩

/--
Compares two floating point numbers for strict inequality.

This function does not reduce in the kernel. It is compiled to the C inequality operator.
-/
@[extern "lean_float_decLt"] opaque Float.decLt (a b : Float) : Decidable (a < b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLt a b

/--
Compares two floating point numbers for non-strict inequality.

This function does not reduce in the kernel. It is compiled to the C inequality operator.
-/
@[extern "lean_float_decLe"] opaque Float.decLe (a b : Float) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLe a b

instance floatDecLt (a b : Float) : Decidable (a < b) := Float.decLt a b
instance floatDecLe (a b : Float) : Decidable (a ≤ b) := Float.decLe a b

/--
Converts a floating-point number to a string.

This function does not reduce in the kernel.
-/
@[extern "lean_float_to_string"] opaque Float.toString : Float → String

/--
Converts a floating-point number to an 8-bit unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt8`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `UInt8` value (i.e. `UInt8.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float_to_uint8"] opaque Float.toUInt8 : Float → UInt8
/--
Converts a floating-point number to a 16-bit unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt16`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `UInt16` value (i.e. `UInt16.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float_to_uint16"] opaque Float.toUInt16 : Float → UInt16
/--
Converts a floating-point number to a 32-bit unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt32`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `UInt32` value (i.e. `UInt32.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float_to_uint32"] opaque Float.toUInt32 : Float → UInt32
/--
Converts a floating-point number to a 64-bit unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt64`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `UInt64` value (i.e. `UInt64.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float_to_uint64"] opaque Float.toUInt64 : Float → UInt64
/--
Converts a floating-point number to a word-sized unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `USize`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `USize` value (i.e. `USize.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float_to_usize"] opaque Float.toUSize : Float → USize

/--
Checks whether a floating point number is `NaN` (“not a number”) value.

`NaN` values result from operations that might otherwise be errors, such as dividing zero by zero.

This function does not reduce in the kernel. It is compiled to the C operator `isnan`.
-/
@[extern "lean_float_isnan"] opaque Float.isNaN : Float → Bool

/--
Checks whether a floating-point number is finite, that is, whether it is normal, subnormal, or zero,
but not infinite or `NaN`.

This function does not reduce in the kernel. It is compiled to the C operator `isfinite`.
-/
@[extern "lean_float_isfinite"] opaque Float.isFinite : Float → Bool

/--
Checks whether a floating-point number is a positive or negative infinite number, but not a finite
number or `NaN`.

This function does not reduce in the kernel. It is compiled to the C operator `isinf`.
-/
@[extern "lean_float_isinf"] opaque Float.isInf : Float → Bool

/--
Splits the given float `x` into a significand/exponent pair `(s, i)` such that `x = s * 2^i` where
`s ∈ (-1;-0.5] ∪ [0.5; 1)`. Returns an undefined value if `x` is not finite.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`frexp`.
-/
@[extern "lean_float_frexp"] opaque Float.frExp : Float → Float × Int

instance : ToString Float where
  toString := Float.toString

/-- Obtains the `Float` whose value is the same as the given `UInt8`. -/
@[extern "lean_uint8_to_float"] opaque UInt8.toFloat (n : UInt8) : Float
/-- Obtains the `Float` whose value is the same as the given `UInt16`. -/
@[extern "lean_uint16_to_float"] opaque UInt16.toFloat (n : UInt16) : Float
/-- Obtains the `Float` whose value is the same as the given `UInt32`. -/
@[extern "lean_uint32_to_float"] opaque UInt32.toFloat (n : UInt32) : Float
/--
Obtains a `Float` whose value is near the given `UInt64`.

It will be exactly the value of the given `UInt64` if such a `Float` exists. If no such `Float`
exists, the returned value will either be the smallest `Float` that is larger than the given value,
or the largest `Float` that is smaller than the given value.

This function is opaque in the kernel, but is overridden at runtime with an efficient
implementation.
-/
@[extern "lean_uint64_to_float"] opaque UInt64.toFloat (n : UInt64) : Float
/--
Obtains a `Float` whose value is near the given `USize`.

It will be exactly the value of the given `USize` if such a `Float` exists. If no such `Float`
exists, the returned value will either be the smallest `Float` that is larger than the given value,
or the largest `Float` that is smaller than the given value.

This function is opaque in the kernel, but is overridden at runtime with an efficient
implementation.
-/
@[extern "lean_usize_to_float"] opaque USize.toFloat (n : USize) : Float

instance : Inhabited Float where
  default := UInt64.toFloat 0

instance : Repr Float where
  reprPrec n prec := if n < UInt64.toFloat 0 then Repr.addAppParen (toString n) prec else toString n

instance : ReprAtom Float  := ⟨⟩

/--
Computes the sine of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`sin`.
-/
@[extern "sin"] opaque Float.sin : Float → Float
/--
Computes the cosine of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`cos`.
-/
@[extern "cos"] opaque Float.cos : Float → Float
/--
Computes the tangent of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`tan`.
-/
@[extern "tan"] opaque Float.tan : Float → Float
/--
Computes the arc sine (inverse sine) of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`asin`.
-/
@[extern "asin"] opaque Float.asin : Float → Float
/--
Computes the arc cosine (inverse cosine) of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`acos`.
-/
@[extern "acos"] opaque Float.acos : Float → Float
/--
Computes the arc tangent (inverse tangent) of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`atan`.
-/
@[extern "atan"] opaque Float.atan : Float → Float
/--
Computes the arc tangent (inverse tangent) of `y / x` in radians, in the range `-π`–`π`. The signs
of the arguments determine the quadrant of the result.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`atan2`.
-/
@[extern "atan2"] opaque Float.atan2 (y x : Float) : Float
/--
Computes the hyperbolic sine of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`sinh`.
-/
@[extern "sinh"] opaque Float.sinh : Float → Float
/--
Computes the hyperbolic cosine of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`cosh`.
-/
@[extern "cosh"] opaque Float.cosh : Float → Float
/--
Computes the hyperbolic tangent of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`tanh`.
-/
@[extern "tanh"] opaque Float.tanh : Float → Float
/--
Computes the hyperbolic arc sine (inverse sine) of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`asinh`.
-/
@[extern "asinh"] opaque Float.asinh : Float → Float
/--
Computes the hyperbolic arc cosine (inverse cosine) of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`acosh`.
-/
@[extern "acosh"] opaque Float.acosh : Float → Float
/--
Computes the hyperbolic arc tangent (inverse tangent) of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`atanh`.
-/
@[extern "atanh"] opaque Float.atanh : Float → Float
/--
Computes the exponential `e^x` of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`exp`.
-/
@[extern "exp"] opaque Float.exp (x : Float) : Float
/--
Computes the base-2 exponential `2^x` of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`exp2`.
-/
@[extern "exp2"] opaque Float.exp2 (x : Float) : Float
/--
Computes the natural logarithm `ln x` of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`log`.
-/
@[extern "log"] opaque Float.log (x : Float) : Float
/--
Computes the base-2 logarithm of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`log2`.
-/
@[extern "log2"] opaque Float.log2 : Float → Float
/--
Computes the base-10 logarithm of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`log10`.
-/
@[extern "log10"] opaque Float.log10 : Float → Float
/--
Raises one floating-point number to the power of another. Typically used via the `^` operator.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`pow`.
-/
@[extern "pow"] opaque Float.pow : Float → Float → Float
/--
Computes the square root of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`sqrt`.
-/
@[extern "sqrt"] opaque Float.sqrt : Float → Float
/--
Computes the cube root of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`cbrt`.
-/
@[extern "cbrt"] opaque Float.cbrt : Float → Float
/--
Computes the ceiling of a floating-point number, which is the smallest integer that's no smaller
than the given number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`ceil`.

Examples:
 * `Float.ceil 1.5 = 2`
 * `Float.ceil (-1.5) = (-1)`
-/
@[extern "ceil"] opaque Float.ceil : Float → Float
/--
Computes the floor of a floating-point number, which is the largest integer that's no larger
than the given number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`floor`.

Examples:
 * `Float.floor 1.5 = 1`
 * `Float.floor (-1.5) = (-2)`
-/
@[extern "floor"] opaque Float.floor : Float → Float
/--
Rounds to the nearest integer, rounding away from zero at half-way points.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`round`.
-/
@[extern "round"] opaque Float.round : Float → Float
/--
Computes the absolute value of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`fabs`.
-/
@[extern "fabs"] opaque Float.abs : Float → Float

instance : HomogeneousPow Float := ⟨Float.pow⟩

instance : Min Float := minOfLe

instance : Max Float := maxOfLe

/--
Efficiently computes `x * 2^i`.

This function does not reduce in the kernel.
-/
@[extern "lean_float_scaleb"]
opaque Float.scaleB (x : Float) (i : @& Int) : Float

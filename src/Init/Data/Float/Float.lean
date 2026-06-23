/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Julia M. Himmel
-/
module

prelude
public import Init.Data.ToString.Basic
public import Init.Data.Float.Model.Float

@[expose] public section

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

Like other low-level types, `Float` is special-cased by the Lean compiler to correspond to the C
`double` type. From the point of view of Lean's logic, `Float` is equivalent to `Float.Model` (via
the functions `Float.toModel` and `Float.ofModel`), which is itself a subtype of `UInt64`. Some of
the operations on `Float` are defined in terms of their `Float.Model` counterparts, while others
are opaque to Lean's kernel.
-/
structure Float where
  /-- Constructs a `Float` from a `Float.Model`. -/
  ofModel ::
  /-- Converts a `Float` into a `Float.Model`. -/
  toModel : Float.Model

attribute [extern "lean_float_to_bits"] Float.toModel
attribute [extern "lean_float_of_bits"] Float.ofModel

instance : Nonempty Float :=
  ⟨⟨default⟩⟩

/--
Adds two 64-bit floating-point numbers according to IEEE 754. Typically used via the `+` operator.

This function has a logical model in terms of `Float.Model`. It is compiled to the C addition operator.
-/
@[extern "lean_float_add"] def Float.add : Float → Float → Float :=
  fun a b => .ofModel (a.toModel + b.toModel)

/--
Subtracts 64-bit floating-point numbers according to IEEE 754. Typically used via the `-` operator.

This function has a logical model in terms of `Float.Model`. It is compiled to the C subtraction operator.
-/
@[extern "lean_float_sub"] def Float.sub : Float → Float → Float :=
  fun a b => .ofModel (a.toModel - b.toModel)
/--
Multiplies 64-bit floating-point numbers according to IEEE 754. Typically used via the `*` operator.

This function has a logical model in terms of `Float.Model`. It is compiled to the C multiplication operator.
-/
@[extern "lean_float_mul"] def Float.mul : Float → Float → Float :=
  fun a b => .ofModel (a.toModel * b.toModel)
/--
Divides 64-bit floating-point numbers according to IEEE 754. Typically used via the `/` operator.

In Lean, division by zero typically yields zero. For `Float`, it instead yields either `Inf`,
`-Inf`, or `NaN`.

This function has a logical model in terms of `Float.Model`. It is compiled to the C division operator.
-/
@[extern "lean_float_div"] def Float.div : Float → Float → Float :=
  fun a b => .ofModel (a.toModel / b.toModel)

/--
Negates 64-bit floating-point numbers according to IEEE 754. Typically used via the `-` prefix
operator.

This function has a logical model in terms of `Float.Model`. It is compiled to the C negation operator.
-/
@[extern "lean_float_negate"] def Float.neg : Float → Float :=
  fun a => .ofModel (-a.toModel)

/--
Strict inequality of floating-point numbers. Typically used via the `<` operator.
-/
@[extern "lean_float_decLt"] def Float.lt : Float → Float → Bool :=
  fun a b => a.toModel < b.toModel

/--
Non-strict inequality of floating-point numbers. Typically used via the `≤` operator.
-/
@[extern "lean_float_decLe"] def Float.le : Float → Float → Bool :=
  fun a b => a.toModel ≤ b.toModel

/--
Bit-for-bit conversion from `UInt64`. Interprets a `UInt64` as a `Float`, ignoring the numeric value
and treating the `UInt64`'s bit pattern as a `Float`.

`Float`s and `UInt64`s have the same endianness on all supported platforms. IEEE 754 very precisely
specifies the bit layout of floats.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_of_bits"] def Float.ofBits : UInt64 → Float :=
  fun a => .ofModel <| .ofBits a

/--
Bit-for-bit conversion to `UInt64`. Interprets a `Float` as a `UInt64`, ignoring the numeric value
and treating the `Float`'s bit pattern as a `UInt64`.

`Float`s and `UInt64`s have the same endianness on all supported platforms. IEEE 754 very precisely
specifies the bit layout of floats.

This function is distinct from `Float.toUInt64`, which attempts to preserve the numeric value rather
than reinterpreting the bit pattern.
-/
@[extern "lean_float_to_bits"] def Float.toBits : Float → UInt64 :=
  fun a => a.toModel.toBits

instance : Add Float := ⟨Float.add⟩
instance : Sub Float := ⟨Float.sub⟩
instance : Mul Float := ⟨Float.mul⟩
instance : Div Float := ⟨Float.div⟩
instance : Neg Float := ⟨Float.neg⟩
instance : LT Float  := ⟨fun a b => a.lt b⟩
instance : LE Float  := ⟨fun a b => a.le b⟩

/--
Checks whether two floating-point numbers are equal according to IEEE 754.

Floating-point equality does not correspond with propositional equality. In particular, it is not
reflexive since `NaN != NaN`, and it is not a congruence because `0.0 == -0.0`, but
`1.0 / 0.0 != 1.0 / -0.0`.

This function does not reduce in the kernel. It is compiled to the C equality operator.
-/
@[extern "lean_float_beq"] def Float.beq (a b : Float) : Bool :=
  a.toModel == b.toModel

instance : BEq Float := ⟨Float.beq⟩

/--
Compares two floating point numbers for strict inequality.

This function does not reduce in the kernel. It is compiled to the C inequality operator.
-/
@[extern "lean_float_decLt"] instance Float.decLt (a b : Float) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.lt b))

/--
Compares two floating point numbers for non-strict inequality.

This function does not reduce in the kernel. It is compiled to the C inequality operator.
-/
@[extern "lean_float_decLe"] instance Float.decLe (a b : Float) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.le b))

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

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_uint8"] def Float.toUInt8 : Float → UInt8 :=
  fun a => a.toModel.toUInt8
/--
Converts a floating-point number to a 16-bit unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt16`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `UInt16` value (i.e. `UInt16.size - 1`) if the float is larger than it.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_uint16"] def Float.toUInt16 : Float → UInt16 :=
  fun a => a.toModel.toUInt16
/--
Converts a floating-point number to a 32-bit unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt32`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `UInt32` value (i.e. `UInt32.size - 1`) if the float is larger than it.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_uint32"] def Float.toUInt32 : Float → UInt32 :=
  fun a => a.toModel.toUInt32
/--
Converts a floating-point number to a 64-bit unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt64`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `UInt64` value (i.e. `UInt64.size - 1`) if the float is larger than it.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_uint64"] def Float.toUInt64 : Float → UInt64 :=
  fun a => a.toModel.toUInt64
/--
Converts a floating-point number to a word-sized unsigned integer.

If the given `Float` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `USize`. Returns `0` if the `Float` is negative or `NaN`, and returns the
largest `USize` value (i.e. `USize.size - 1`) if the float is larger than it.

This function has a logical model in terms of `Float.Model`.
-/
@[extern "lean_float_to_usize"] def Float.toUSize : Float → USize :=
  fun a => a.toModel.toUSize

/--
Checks whether a floating point number is `NaN` (“not a number”) value.

`NaN` values result from operations that might otherwise be errors, such as dividing zero by zero.

This function has a logical model in terms of `Float.Model`. It is compiled to the C operator `isnan`.
-/
@[extern "lean_float_isnan"] def Float.isNaN : Float → Bool :=
  fun a => a.toModel.isNaN

/--
Checks whether a floating-point number is finite, that is, whether it is normal, subnormal, or zero,
but not infinite or `NaN`.

This function has a logical model in terms of `Float.Model`. It is compiled to the C operator `isfinite`.
-/
@[extern "lean_float_isfinite"] def Float.isFinite : Float → Bool :=
  fun a => a.toModel.isFinite

/--
Checks whether a floating-point number is a positive or negative infinite number, but not a finite
number or `NaN`.

This function has a logical model in terms of `Float.Model`. It is compiled to the C operator `isinf`.
-/
@[extern "lean_float_isinf"] def Float.isInf : Float → Bool :=
  fun a => a.toModel.isInf

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
@[extern "lean_uint8_to_float"] def UInt8.toFloat (n : UInt8) : Float :=
  .ofModel (.ofUInt8 n)
/-- Obtains the `Float` whose value is the same as the given `UInt16`. -/
@[extern "lean_uint16_to_float"] def UInt16.toFloat (n : UInt16) : Float :=
  .ofModel (.ofUInt16 n)
/-- Obtains the `Float` whose value is the same as the given `UInt32`. -/
@[extern "lean_uint32_to_float"] def UInt32.toFloat (n : UInt32) : Float :=
  .ofModel (.ofUInt32 n)
/--
Obtains a `Float` whose value is near the given `UInt64`.

It will be exactly the value of the given `UInt64` if such a `Float` exists. If no such `Float`
exists, the returned value will either be the smallest `Float` that is larger than the given value,
or the largest `Float` that is smaller than the given value.

This function has a logical model in terms of `Float.Model`, but is overridden at runtime with an
efficient implementation.
-/
@[extern "lean_uint64_to_float"] def UInt64.toFloat (n : UInt64) : Float :=
  .ofModel (.ofUInt64 n)
/--
Obtains a `Float` whose value is near the given `USize`.

It will be exactly the value of the given `USize` if such a `Float` exists. If no such `Float`
exists, the returned value will either be the smallest `Float` that is larger than the given value,
or the largest `Float` that is smaller than the given value.

This function has a logical model in terms of `Float.Model`, but is overridden at runtime with an
efficient implementation.
-/
@[extern "lean_usize_to_float"] def USize.toFloat (n : USize) : Float :=
  .ofModel (.ofUSize n)

instance : Inhabited Float where
  default := UInt64.toFloat 0

protected def Float.repr (n : Float) (prec : Nat) : Std.Format :=
  if n < UInt64.toFloat 0 then Repr.addAppParen (toString n) prec else toString n

instance : Repr Float where
  reprPrec := Float.repr

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

This function has a logical model in terms of `Float.Model`. It is implemented in compiled code by the
C function `sqrt`.
-/
@[extern "sqrt"] def Float.sqrt : Float → Float :=
  fun a => .ofModel a.toModel.sqrt
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

This function has a logical model in terms of `Float.Model`. It is implemented in compiled code by the
C function `fabs`.
-/
@[extern "fabs"] def Float.abs : Float → Float :=
  fun a => .ofModel a.toModel.abs

instance : HomogeneousPow Float := ⟨Float.pow⟩

instance : Min Float := minOfLe

instance : Max Float := maxOfLe

/--
Efficiently computes `x * 2^i`.

This function does not reduce in the kernel.
-/
@[extern "lean_float_scaleb"]
opaque Float.scaleB (x : Float) (i : @& Int) : Float

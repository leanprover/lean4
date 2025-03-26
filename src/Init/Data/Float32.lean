/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Data.Int.Basic
import Init.Data.ToString.Basic
import Init.Data.Float

-- Just show FloatSpec is inhabited.
opaque float32Spec : FloatSpec := {
  float := Unit,
  val   := (),
  lt    := fun _ _ => True,
  le    := fun _ _ => True,
  decLt := fun _ _ => inferInstanceAs (Decidable True),
  decLe := fun _ _ => inferInstanceAs (Decidable True)
}

/--
32-bit floating-point numbers.

`Float32` corresponds to the IEEE 754 *binary32* format (`float` in C or `f32` in Rust).
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
structure Float32 where
  val : float32Spec.float

instance : Nonempty Float32 := ⟨{ val := float32Spec.val }⟩

/--
Adds two 32-bit floating-point numbers according to IEEE 754. Typically used via the `+` operator.

This function does not reduce in the kernel. It is compiled to the C addition operator.
-/
@[extern "lean_float32_add"] opaque Float32.add : Float32 → Float32 → Float32
/--
Subtracts 32-bit floating-point numbers according to IEEE 754. Typically used via the `-` operator.

This function does not reduce in the kernel. It is compiled to the C subtraction operator.
-/
@[extern "lean_float32_sub"] opaque Float32.sub : Float32 → Float32 → Float32
/--
Multiplies 32-bit floating-point numbers according to IEEE 754. Typically used via the `*` operator.

This function does not reduce in the kernel. It is compiled to the C multiplication operator.
-/
@[extern "lean_float32_mul"] opaque Float32.mul : Float32 → Float32 → Float32
/--
Divides 32-bit floating-point numbers according to IEEE 754. Typically used via the `/` operator.

In Lean, division by zero typically yields zero. For `Float32`, it instead yields either `Inf`,
`-Inf`, or `NaN`.

This function does not reduce in the kernel. It is compiled to the C division operator.
-/
@[extern "lean_float32_div"] opaque Float32.div : Float32 → Float32 → Float32
/--
Negates 32-bit floating-point numbers according to IEEE 754. Typically used via the `-` prefix
operator.

This function does not reduce in the kernel. It is compiled to the C negation operator.
-/
@[extern "lean_float32_negate"] opaque Float32.neg : Float32 → Float32

set_option bootstrap.genMatcherCode false
/--
Strict inequality of floating-point numbers. Typically used via the `<` operator.
-/
def Float32.lt : Float32 → Float32 → Prop := fun a b =>
  match a, b with
  | ⟨a⟩, ⟨b⟩ => float32Spec.lt a b

/--
Non-strict inequality of floating-point numbers. Typically used via the `≤` operator.
-/
def Float32.le : Float32 → Float32 → Prop := fun a b =>
  float32Spec.le a.val b.val

/--
Bit-for-bit conversion from `UInt32`. Interprets a `UInt32` as a `Float32`, ignoring the numeric
value and treating the `UInt32`'s bit pattern as a `Float32`.

`Float32`s and `UInt32`s have the same endianness on all supported platforms. IEEE 754 very
precisely specifies the bit layout of floats.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_of_bits"] opaque Float32.ofBits : UInt32 → Float32


/--
Bit-for-bit conversion to `UInt32`. Interprets a `Float32` as a `UInt32`, ignoring the numeric value
and treating the `Float32`'s bit pattern as a `UInt32`.

`Float32`s and `UInt32`s have the same endianness on all supported platforms. IEEE 754 very
precisely specifies the bit layout of floats.

This function is distinct from `Float.toUInt32`, which attempts to preserve the numeric value rather
than reinterpreting the bit pattern.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_to_bits"] opaque Float32.toBits : Float32 → UInt32

instance : Add Float32 := ⟨Float32.add⟩
instance : Sub Float32 := ⟨Float32.sub⟩
instance : Mul Float32 := ⟨Float32.mul⟩
instance : Div Float32 := ⟨Float32.div⟩
instance : Neg Float32 := ⟨Float32.neg⟩
instance : LT Float32  := ⟨Float32.lt⟩
instance : LE Float32  := ⟨Float32.le⟩

/--
Checks whether two floating-point numbers are equal according to IEEE 754.

Floating-point equality does not correspond with propositional equality. In particular, it is not
reflexive since `NaN != NaN`, and it is not a congruence because `0.0 == -0.0`, but
`1.0 / 0.0 != 1.0 / -0.0`.

This function does not reduce in the kernel. It is compiled to the C equality operator.
-/
@[extern "lean_float32_beq"] opaque Float32.beq (a b : Float32) : Bool

instance : BEq Float32 := ⟨Float32.beq⟩

/--
Compares two floating point numbers for strict inequality.

This function does not reduce in the kernel. It is compiled to the C inequality operator.
-/
@[extern "lean_float32_decLt"] opaque Float32.decLt (a b : Float32) : Decidable (a < b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => float32Spec.decLt a b

/--
Compares two floating point numbers for non-strict inequality.

This function does not reduce in the kernel. It is compiled to the C inequality operator.
-/
@[extern "lean_float32_decLe"] opaque Float32.decLe (a b : Float32) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => float32Spec.decLe a b

instance float32DecLt (a b : Float32) : Decidable (a < b) := Float32.decLt a b
instance float32DecLe (a b : Float32) : Decidable (a ≤ b) := Float32.decLe a b

/--
Converts a floating-point number to a string.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_to_string"] opaque Float32.toString : Float32 → String
/--
Converts a floating-point number to an 8-bit unsigned integer.

If the given `Float32` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt8`. Returns `0` if the `Float32` is negative or `NaN`, and returns the
largest `UInt8` value (i.e. `UInt8.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_to_uint8"] opaque Float32.toUInt8 : Float32 → UInt8
/--
Converts a floating-point number to a 16-bit unsigned integer.

If the given `Float32` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt16`. Returns `0` if the `Float32` is negative or `NaN`, and returns
the largest `UInt16` value (i.e. `UInt16.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_to_uint16"] opaque Float32.toUInt16 : Float32 → UInt16
/--
Converts a floating-point number to a 32-bit unsigned integer.

If the given `Float32` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt32`. Returns `0` if the `Float32` is negative or `NaN`, and returns
the largest `UInt32` value (i.e. `UInt32.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_to_uint32"] opaque Float32.toUInt32 : Float32 → UInt32
/--
Converts a floating-point number to a 64-bit unsigned integer.

If the given `Float32` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `UInt64`. Returns `0` if the `Float32` is negative or `NaN`, and returns
the largest `UInt64` value (i.e. `UInt64.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_to_uint64"] opaque Float32.toUInt64 : Float32 → UInt64
/--
Converts a floating-point number to a word-sized unsigned integer.

If the given `Float32` is non-negative, truncates the value to a positive integer, rounding down and
clamping to the range of `USize`. Returns `0` if the `Float32` is negative or `NaN`, and returns the
largest `USize` value (i.e. `USize.size - 1`) if the float is larger than it.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_to_usize"] opaque Float32.toUSize : Float32 → USize

/--
Checks whether a floating point number is `NaN` ("not a number") value.

`NaN` values result from operations that might otherwise be errors, such as dividing zero by zero.

This function does not reduce in the kernel. It is compiled to the C operator `isnan`.
-/
@[extern "lean_float32_isnan"] opaque Float32.isNaN : Float32 → Bool
/--
Checks whether a floating-point number is finite, that is, whether it is normal, subnormal, or zero,
but not infinite or `NaN`.

This function does not reduce in the kernel. It is compiled to the C operator `isfinite`.
-/
@[extern "lean_float32_isfinite"] opaque Float32.isFinite : Float32 → Bool
/--
Checks whether a floating-point number is a positive or negative infinite number, but not a finite
number or `NaN`.

This function does not reduce in the kernel. It is compiled to the C operator `isinf`.
-/
@[extern "lean_float32_isinf"] opaque Float32.isInf : Float32 → Bool
/--
Splits the given float `x` into a significand/exponent pair `(s, i)` such that `x = s * 2^i` where
`s ∈ (-1;-0.5] ∪ [0.5; 1)`. Returns an undefined value if `x` is not finite.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`frexp`.
-/
@[extern "lean_float32_frexp"] opaque Float32.frExp : Float32 → Float32 × Int

instance : ToString Float32 where
  toString := Float32.toString

/-- Obtains the `Float32` whose value is the same as the given `UInt8`. -/
@[extern "lean_uint8_to_float32"] opaque UInt8.toFloat32 (n : UInt8) : Float32
/-- Obtains the `Float32` whose value is the same as the given `UInt16`. -/
@[extern "lean_uint16_to_float32"] opaque UInt16.toFloat32 (n : UInt16) : Float32
/--
Obtains a `Float32` whose value is near the given `UInt32`.

It will be exactly the value of the given `UInt32` if such a `Float32` exists. If no such `Float32`
exists, the returned value will either be the smallest `Float32` that is larger than the given
value, or the largest `Float32` that is smaller than the given value.

This function is opaque in the kernel, but is overridden at runtime with an efficient
implementation.
-/
@[extern "lean_uint32_to_float32"] opaque UInt32.toFloat32 (n : UInt32) : Float32
/--
Obtains a `Float32` whose value is near the given `UInt64`.

It will be exactly the value of the given `UInt64` if such a `Float32` exists. If no such `Float32`
exists, the returned value will either be the smallest `Float32` that is larger than the given
value, or the largest `Float32` that is smaller than the given value.

This function is opaque in the kernel, but is overridden at runtime with an efficient
implementation.
-/
@[extern "lean_uint64_to_float32"] opaque UInt64.toFloat32 (n : UInt64) : Float32
/-- Obtains a `Float32` whose value is near the given `USize`.

It will be exactly the value of the given `USize` if such a `Float32` exists. If no such `Float32`
exists, the returned value will either be the smallest `Float32` that is larger than the given
value, or the largest `Float32` that is smaller than the given value.

This function is opaque in the kernel, but is overridden at runtime with an efficient
implementation.
-/
@[extern "lean_usize_to_float32"] opaque USize.toFloat32 (n : USize) : Float32

instance : Inhabited Float32 where
  default := UInt64.toFloat32 0

instance : Repr Float32 where
  reprPrec n prec := if n < UInt64.toFloat32 0 then Repr.addAppParen (toString n) prec else toString n

instance : ReprAtom Float32  := ⟨⟩

/--
Computes the sine of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`sinf`.
-/
@[extern "sinf"] opaque Float32.sin : Float32 → Float32
/--
Computes the cosine of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`cosf`.
-/
@[extern "cosf"] opaque Float32.cos : Float32 → Float32
/--
Computes the tangent of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`tanf`.
-/
@[extern "tanf"] opaque Float32.tan : Float32 → Float32
/--
Computes the arc sine (inverse sine) of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`asinf`.
-/
@[extern "asinf"] opaque Float32.asin : Float32 → Float32
/--
Computes the arc cosine (inverse cosine) of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`acosf`.
-/
@[extern "acosf"] opaque Float32.acos : Float32 → Float32
/--
Computes the arc tangent (inverse tangent) of a floating-point number in radians.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`atanf`.
-/
@[extern "atanf"] opaque Float32.atan : Float32 → Float32
/--
Computes the arc tangent (inverse tangent) of `y / x` in radians, in the range `-π`–`π`. The signs
of the arguments determine the quadrant of the result.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`atan2f`.
-/
@[extern "atan2f"] opaque Float32.atan2 : Float32 → Float32 → Float32
/--
Computes the hyperbolic sine of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`sinhf`.
-/
@[extern "sinhf"] opaque Float32.sinh : Float32 → Float32
/--
Computes the hyperbolic cosine of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`coshf`.
-/
@[extern "coshf"] opaque Float32.cosh : Float32 → Float32
/--
Computes the hyperbolic tangent of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`tanhf`.
-/
@[extern "tanhf"] opaque Float32.tanh : Float32 → Float32
/--
Computes the hyperbolic arc sine (inverse sine) of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`asinhf`.
-/
@[extern "asinhf"] opaque Float32.asinh : Float32 → Float32
/--
Computes the hyperbolic arc cosine (inverse cosine) of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`acoshf`.
-/
@[extern "acoshf"] opaque Float32.acosh : Float32 → Float32
/--
Computes the hyperbolic arc tangent (inverse tangent) of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`atanhf`.
-/
@[extern "atanhf"] opaque Float32.atanh : Float32 → Float32
/--
Computes the exponential `e^x` of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`expf`.
-/
@[extern "expf"] opaque Float32.exp : Float32 → Float32
/--
Computes the base-2 exponential `2^x` of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`exp2f`.
-/
@[extern "exp2f"] opaque Float32.exp2 : Float32 → Float32
/--
Computes the natural logarithm `ln x` of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`logf`.
-/
@[extern "logf"] opaque Float32.log : Float32 → Float32
/--
Computes the base-2 logarithm of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`log2f`.
-/
@[extern "log2f"] opaque Float32.log2 : Float32 → Float32
/--
Computes the base-10 logarithm of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`log10f`.
-/
@[extern "log10f"] opaque Float32.log10 : Float32 → Float32
/--
Raises one floating-point number to the power of another. Typically used via the `^` operator.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`powf`.
-/
@[extern "powf"] opaque Float32.pow : Float32 → Float32 → Float32
/--
Computes the square root of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`sqrtf`.
-/
@[extern "sqrtf"] opaque Float32.sqrt : Float32 → Float32
/--
Computes the cube root of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`cbrtf`.
-/
@[extern "cbrtf"] opaque Float32.cbrt : Float32 → Float32
/--
Computes the ceiling of a floating-point number, which is the smallest integer that's no smaller
than the given number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`ceilf`.

Examples:
 * `Float32.ceil 1.5 = 2`
 * `Float32.ceil (-1.5) = (-1)`
-/
@[extern "ceilf"] opaque Float32.ceil : Float32 → Float32
/--
Computes the floor of a floating-point number, which is the largest integer that's no larger
than the given number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`floorf`.

Examples:
 * `Float32.floor 1.5 = 1`
 * `Float32.floor (-1.5) = (-2)`
-/
@[extern "floorf"] opaque Float32.floor : Float32 → Float32
/--
Rounds to the nearest integer, rounding away from zero at half-way points.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`roundf`.
-/
@[extern "roundf"] opaque Float32.round : Float32 → Float32
/--
Computes the absolute value of a floating-point number.

This function does not reduce in the kernel. It is implemented in compiled code by the C function
`fabsf`.
-/
@[extern "fabsf"] opaque Float32.abs : Float32 → Float32

instance : HomogeneousPow Float32 := ⟨Float32.pow⟩

instance : Min Float32 := minOfLe

instance : Max Float32 := maxOfLe

/--
Efficiently computes `x * 2^i`.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_scaleb"]
opaque Float32.scaleB (x : Float32) (i : @& Int) : Float32

/--
Converts a 32-bit floating-point number to a 64-bit floating-point number.

This function does not reduce in the kernel.
-/
@[extern "lean_float32_to_float"] opaque Float32.toFloat : Float32 → Float
/--
Converts a 64-bit floating-point number to a 32-bit floating-point number.
This may lose precision.

This function does not reduce in the kernel.
-/
@[extern "lean_float_to_float32"] opaque Float.toFloat32 : Float → Float32

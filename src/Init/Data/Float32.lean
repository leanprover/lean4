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

/-- Native floating point type, corresponding to the IEEE 754 *binary32* format
(`float` in C or `f32` in Rust). -/
structure Float32 where
  val : float32Spec.float

instance : Nonempty Float32 := ⟨{ val := float32Spec.val }⟩

@[extern "lean_float32_add"] opaque Float32.add : Float32 → Float32 → Float32
@[extern "lean_float32_sub"] opaque Float32.sub : Float32 → Float32 → Float32
@[extern "lean_float32_mul"] opaque Float32.mul : Float32 → Float32 → Float32
@[extern "lean_float32_div"] opaque Float32.div : Float32 → Float32 → Float32
@[extern "lean_float32_negate"] opaque Float32.neg : Float32 → Float32

set_option bootstrap.genMatcherCode false
def Float32.lt : Float32 → Float32 → Prop := fun a b =>
  match a, b with
  | ⟨a⟩, ⟨b⟩ => float32Spec.lt a b

def Float32.le : Float32 → Float32 → Prop := fun a b =>
  float32Spec.le a.val b.val

/--
Raw transmutation from `UInt32`.

Float32s and UInts have the same endianness on all supported platforms.
IEEE 754 very precisely specifies the bit layout of floats.
-/
@[extern "lean_float32_of_bits"] opaque Float32.ofBits : UInt32 → Float32

/--
Raw transmutation to `UInt32`.

Float32s and UInts have the same endianness on all supported platforms.
IEEE 754 very precisely specifies the bit layout of floats.

Note that this function is distinct from `Float32.toUInt32`, which attempts
to preserve the numeric value, and not the bitwise value.
-/
@[extern "lean_float32_to_bits"] opaque Float32.toBits : Float32 → UInt32

instance : Add Float32 := ⟨Float32.add⟩
instance : Sub Float32 := ⟨Float32.sub⟩
instance : Mul Float32 := ⟨Float32.mul⟩
instance : Div Float32 := ⟨Float32.div⟩
instance : Neg Float32 := ⟨Float32.neg⟩
instance : LT Float32  := ⟨Float32.lt⟩
instance : LE Float32  := ⟨Float32.le⟩

/-- Note: this is not reflexive since `NaN != NaN`.-/
@[extern "lean_float32_beq"] opaque Float32.beq (a b : Float32) : Bool

instance : BEq Float32 := ⟨Float32.beq⟩

@[extern "lean_float32_decLt"] opaque Float32.decLt (a b : Float32) : Decidable (a < b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => float32Spec.decLt a b

@[extern "lean_float32_decLe"] opaque Float32.decLe (a b : Float32) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => float32Spec.decLe a b

instance float32DecLt (a b : Float32) : Decidable (a < b) := Float32.decLt a b
instance float32DecLe (a b : Float32) : Decidable (a ≤ b) := Float32.decLe a b

@[extern "lean_float32_to_string"] opaque Float32.toString : Float32 → String
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt8` (including Inf), returns the maximum value of `UInt8`
(i.e. `UInt8.size - 1`).
-/
@[extern "lean_float32_to_uint8"] opaque Float32.toUInt8 : Float32 → UInt8
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt16` (including Inf), returns the maximum value of `UInt16`
(i.e. `UInt16.size - 1`).
-/
@[extern "lean_float32_to_uint16"] opaque Float32.toUInt16 : Float32 → UInt16
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt32` (including Inf), returns the maximum value of `UInt32`
(i.e. `UInt32.size - 1`).
-/
@[extern "lean_float32_to_uint32"] opaque Float32.toUInt32 : Float32 → UInt32
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `UInt64` (including Inf), returns the maximum value of `UInt64`
(i.e. `UInt64.size - 1`).
-/
@[extern "lean_float32_to_uint64"] opaque Float32.toUInt64 : Float32 → UInt64
/-- If the given float is non-negative, truncates the value to the nearest non-negative integer.
If negative or NaN, returns `0`.
If larger than the maximum value for `USize` (including Inf), returns the maximum value of `USize`
(i.e. `USize.size - 1`). This value is platform dependent).
-/
@[extern "lean_float32_to_usize"] opaque Float32.toUSize : Float32 → USize

@[extern "lean_float32_isnan"] opaque Float32.isNaN : Float32 → Bool
@[extern "lean_float32_isfinite"] opaque Float32.isFinite : Float32 → Bool
@[extern "lean_float32_isinf"] opaque Float32.isInf : Float32 → Bool
/-- Splits the given float `x` into a significand/exponent pair `(s, i)`
such that `x = s * 2^i` where `s ∈ (-1;-0.5] ∪ [0.5; 1)`.
Returns an undefined value if `x` is not finite.
-/
@[extern "lean_float32_frexp"] opaque Float32.frExp : Float32 → Float32 × Int

instance : ToString Float32 where
  toString := Float32.toString

@[extern "lean_uint64_to_float32"] opaque UInt64.toFloat32 (n : UInt64) : Float32

instance : Inhabited Float32 where
  default := UInt64.toFloat32 0

instance : Repr Float32 where
  reprPrec n prec := if n < UInt64.toFloat32 0 then Repr.addAppParen (toString n) prec else toString n

instance : ReprAtom Float32  := ⟨⟩

@[extern "sinf"] opaque Float32.sin : Float32 → Float32
@[extern "cosf"] opaque Float32.cos : Float32 → Float32
@[extern "tanf"] opaque Float32.tan : Float32 → Float32
@[extern "asinf"] opaque Float32.asin : Float32 → Float32
@[extern "acosf"] opaque Float32.acos : Float32 → Float32
@[extern "atanf"] opaque Float32.atan : Float32 → Float32
@[extern "atan2f"] opaque Float32.atan2 : Float32 → Float32 → Float32
@[extern "sinhf"] opaque Float32.sinh : Float32 → Float32
@[extern "coshf"] opaque Float32.cosh : Float32 → Float32
@[extern "tanhf"] opaque Float32.tanh : Float32 → Float32
@[extern "asinhf"] opaque Float32.asinh : Float32 → Float32
@[extern "acoshf"] opaque Float32.acosh : Float32 → Float32
@[extern "atanhf"] opaque Float32.atanh : Float32 → Float32
@[extern "expf"] opaque Float32.exp : Float32 → Float32
@[extern "exp2f"] opaque Float32.exp2 : Float32 → Float32
@[extern "logf"] opaque Float32.log : Float32 → Float32
@[extern "log2f"] opaque Float32.log2 : Float32 → Float32
@[extern "log10f"] opaque Float32.log10 : Float32 → Float32
@[extern "powf"] opaque Float32.pow : Float32 → Float32 → Float32
@[extern "sqrtf"] opaque Float32.sqrt : Float32 → Float32
@[extern "cbrtf"] opaque Float32.cbrt : Float32 → Float32
@[extern "ceilf"] opaque Float32.ceil : Float32 → Float32
@[extern "floorf"] opaque Float32.floor : Float32 → Float32
@[extern "roundf"] opaque Float32.round : Float32 → Float32
@[extern "fabsf"] opaque Float32.abs : Float32 → Float32

instance : HomogeneousPow Float32 := ⟨Float32.pow⟩

instance : Min Float32 := minOfLe

instance : Max Float32 := maxOfLe

/--
Efficiently computes `x * 2^i`.
-/
@[extern "lean_float32_scaleb"]
opaque Float32.scaleB (x : Float32) (i : @& Int) : Float32

@[extern "lean_float32_to_float"] opaque Float32.toFloat : Float32 → Float
@[extern "lean_float_to_float32"] opaque Float.toFloat32 : Float → Float32

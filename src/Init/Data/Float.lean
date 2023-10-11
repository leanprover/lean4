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

structure Float where
  val : floatSpec.float

instance : Inhabited Float := ⟨{ val := floatSpec.val }⟩

@[extern "lean_float_add"] opaque Float.add : Float → Float → Float
@[extern "lean_float_sub"] opaque Float.sub : Float → Float → Float
@[extern "lean_float_mul"] opaque Float.mul : Float → Float → Float
@[extern "lean_float_div"] opaque Float.div : Float → Float → Float
@[extern "lean_float_negate"] opaque Float.neg : Float → Float

set_option bootstrap.genMatcherCode false
def Float.lt : Float → Float → Prop := fun a b =>
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.lt a b

def Float.le : Float → Float → Prop := fun a b =>
  floatSpec.le a.val b.val

instance : Add Float := ⟨Float.add⟩
instance : Sub Float := ⟨Float.sub⟩
instance : Mul Float := ⟨Float.mul⟩
instance : Div Float := ⟨Float.div⟩
instance : Neg Float := ⟨Float.neg⟩
instance : LT Float  := ⟨Float.lt⟩
instance : LE Float  := ⟨Float.le⟩

/-- Note: this is not reflexive since `NaN != NaN`.-/
@[extern "lean_float_beq"] opaque Float.beq (a b : Float) : Bool

instance : BEq Float := ⟨Float.beq⟩

@[extern "lean_float_decLt"] opaque Float.decLt (a b : Float) : Decidable (a < b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLt a b

@[extern "lean_float_decLe"] opaque Float.decLe (a b : Float) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLe a b

instance floatDecLt (a b : Float) : Decidable (a < b) := Float.decLt a b
instance floatDecLe (a b : Float) : Decidable (a ≤ b) := Float.decLe a b

@[extern "lean_float_to_string"] opaque Float.toString : Float → String

/-- If the given float is positive, truncates the value to the nearest positive integer.
If negative or larger than the maximum value for UInt8, returns 0. -/
@[extern "lean_float_to_uint8"] opaque Float.toUInt8 : Float → UInt8
/-- If the given float is positive, truncates the value to the nearest positive integer.
If negative or larger than the maximum value for UInt16, returns 0. -/
@[extern "lean_float_to_uint16"] opaque Float.toUInt16 : Float → UInt16
/-- If the given float is positive, truncates the value to the nearest positive integer.
If negative or larger than the maximum value for UInt32, returns 0. -/
@[extern "lean_float_to_uint32"] opaque Float.toUInt32 : Float → UInt32
/-- If the given float is positive, truncates the value to the nearest positive integer.
If negative or larger than the maximum value for UInt64, returns 0. -/
@[extern "lean_float_to_uint64"] opaque Float.toUInt64 : Float → UInt64
/-- If the given float is positive, truncates the value to the nearest positive integer.
If negative or larger than the maximum value for USize, returns 0. -/
@[extern "lean_float_to_usize"] opaque Float.toUSize : Float → USize

@[extern "lean_float_isnan"] opaque Float.isNaN : Float → Bool
@[extern "lean_float_isfinite"] opaque Float.isFinite : Float → Bool
@[extern "lean_float_isinf"] opaque Float.isInf : Float → Bool
/-- Splits the given float `x` into a significand/exponent pair `(s, i)`
such that `x = s * 2^i` where `s ∈ (-1;-0.5] ∪ [0.5; 1)`.
Returns an undefined value if `x` is not finite.
-/
@[extern "lean_float_frexp"] opaque Float.frExp : Float → Float × Int

instance : ToString Float where
  toString := Float.toString

instance : Repr Float where
  reprPrec n _ := Float.toString n

instance : ReprAtom Float  := ⟨⟩

@[extern "lean_uint64_to_float"] opaque UInt64.toFloat (n : UInt64) : Float

@[extern "sin"] opaque Float.sin : Float → Float
@[extern "cos"] opaque Float.cos : Float → Float
@[extern "tan"] opaque Float.tan : Float → Float
@[extern "asin"] opaque Float.asin : Float → Float
@[extern "acos"] opaque Float.acos : Float → Float
@[extern "atan"] opaque Float.atan : Float → Float
@[extern "atan2"] opaque Float.atan2 : Float → Float → Float
@[extern "sinh"] opaque Float.sinh : Float → Float
@[extern "cosh"] opaque Float.cosh : Float → Float
@[extern "tanh"] opaque Float.tanh : Float → Float
@[extern "asinh"] opaque Float.asinh : Float → Float
@[extern "acosh"] opaque Float.acosh : Float → Float
@[extern "atanh"] opaque Float.atanh : Float → Float
@[extern "exp"] opaque Float.exp : Float → Float
@[extern "exp2"] opaque Float.exp2 : Float → Float
@[extern "log"] opaque Float.log : Float → Float
@[extern "log2"] opaque Float.log2 : Float → Float
@[extern "log10"] opaque Float.log10 : Float → Float
@[extern "pow"] opaque Float.pow : Float → Float → Float
@[extern "sqrt"] opaque Float.sqrt : Float → Float
@[extern "cbrt"] opaque Float.cbrt : Float → Float
@[extern "ceil"] opaque Float.ceil : Float → Float
@[extern "floor"] opaque Float.floor : Float → Float
@[extern "round"] opaque Float.round : Float → Float
@[extern "fabs"] opaque Float.abs : Float → Float

instance : HomogeneousPow Float := ⟨Float.pow⟩

instance : Min Float := minOfLe

instance : Max Float := maxOfLe

/--
Efficiently computes `x * 2^i`.
-/
@[extern "lean_float_scaleb"]
opaque Float.scaleB (x : Float) (i : @& Int) : Float

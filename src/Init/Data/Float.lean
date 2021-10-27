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
constant floatSpec : FloatSpec := {
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

@[extern "lean_float_add"]  constant Float.add : Float → Float → Float
@[extern "lean_float_sub"]  constant Float.sub : Float → Float → Float
@[extern "lean_float_mul"]  constant Float.mul : Float → Float → Float
@[extern "lean_float_div"]  constant Float.div : Float → Float → Float
@[extern "lean_float_negate"]   constant Float.neg : Float → Float

set_option bootstrap.genMatcherCode false
def Float.lt  : Float → Float → Prop := fun a b =>
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.lt a b

def Float.le  : Float → Float → Prop := fun a b =>
  floatSpec.le a.val b.val

instance : Add Float       := ⟨Float.add⟩
instance : Sub Float       := ⟨Float.sub⟩
instance : Mul Float       := ⟨Float.mul⟩
instance : Div Float       := ⟨Float.div⟩
instance : Neg Float       := ⟨Float.neg⟩
instance : LT Float        := ⟨Float.lt⟩
instance : LE Float        := ⟨Float.le⟩

@[extern "lean_float_beq"] constant Float.beq (a b : Float) : Bool

instance : BEq Float := ⟨Float.beq⟩

@[extern "lean_float_decLt"]   constant Float.decLt (a b : Float) : Decidable (a < b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLt a b

@[extern "lean_float_decLe"] constant Float.decLe (a b : Float) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLe a b

instance floatDecLt (a b : Float) : Decidable (a < b) := Float.decLt a b
instance floatDecLe (a b : Float) : Decidable (a ≤ b) := Float.decLe a b

@[extern "lean_float_to_string"] constant Float.toString : Float → String

@[extern "lean_float_to_uint8"] constant Float.toUInt8 : Float → UInt8
@[extern "lean_float_to_uint16"] constant Float.toUInt16 : Float → UInt16
@[extern "lean_float_to_uint32"] constant Float.toUInt32 : Float → UInt32
@[extern "lean_float_to_uint64"] constant Float.toUInt64 : Float → UInt64
@[extern "lean_float_to_usize"] constant Float.toUSize : Float → USize

instance : ToString Float where
  toString := Float.toString

instance : Repr Float where
  reprPrec n _ := Float.toString n

instance : ReprAtom Float  := ⟨⟩

@[extern "lean_uint64_to_float"] constant UInt64.toFloat (n : UInt64) : Float

@[extern "sin"] constant Float.sin : Float → Float
@[extern "cos"] constant Float.cos : Float → Float
@[extern "tan"] constant Float.tan : Float → Float
@[extern "asin"] constant Float.asin : Float → Float
@[extern "acos"] constant Float.acos : Float → Float
@[extern "atan"] constant Float.atan : Float → Float
@[extern "atan2"] constant Float.atan2 : Float → Float → Float
@[extern "sinh"] constant Float.sinh : Float → Float
@[extern "cosh"] constant Float.cosh : Float → Float
@[extern "tanh"] constant Float.tanh : Float → Float
@[extern "asinh"] constant Float.asinh : Float → Float
@[extern "acosh"] constant Float.acosh : Float → Float
@[extern "atanh"] constant Float.atanh : Float → Float
@[extern "exp"] constant Float.exp : Float → Float
@[extern "exp2"] constant Float.exp2 : Float → Float
@[extern "log"] constant Float.log : Float → Float
@[extern "log2"] constant Float.log2 : Float → Float
@[extern "log10"] constant Float.log10 : Float → Float
@[extern "pow"] constant Float.pow : Float → Float → Float
@[extern "sqrt"] constant Float.sqrt : Float → Float
@[extern "cbrt"] constant Float.cbrt : Float → Float

instance : Pow Float Float := ⟨Float.pow⟩

/--
Efficiently computes `x * 2^i`.
-/
@[extern "lean_float_scaleb"]
constant Float.scaleB (x : Float) (i : @& Int) : Float

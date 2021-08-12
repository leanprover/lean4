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

@[extern "lean_float_of_nat"] constant Float.ofNat : (@& Nat) → Float
@[extern c inline "#1 + #2"]  constant Float.add : Float → Float → Float
@[extern c inline "#1 - #2"]  constant Float.sub : Float → Float → Float
@[extern c inline "#1 * #2"]  constant Float.mul : Float → Float → Float
@[extern c inline "#1 / #2"]  constant Float.div : Float → Float → Float
@[extern c inline "(- #1)"]   constant Float.neg : Float → Float

def Float.ofInt : Int → Float
  | Int.ofNat n => Float.ofNat n
  | Int.negSucc n => Float.neg (Float.ofNat (Nat.succ n))

set_option bootstrap.genMatcherCode false
def Float.lt  : Float → Float → Prop := fun a b =>
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.lt a b

def Float.le  : Float → Float → Prop := fun a b =>
  floatSpec.le a.val b.val

instance : OfNat Float n   := ⟨Float.ofNat n⟩
instance : Add Float       := ⟨Float.add⟩
instance : Sub Float       := ⟨Float.sub⟩
instance : Mul Float       := ⟨Float.mul⟩
instance : Div Float       := ⟨Float.div⟩
instance : Neg Float       := ⟨Float.neg⟩
instance : LT Float        := ⟨Float.lt⟩
instance : LE Float        := ⟨Float.le⟩

@[extern c inline "#1 == #2"] constant Float.beq (a b : Float) : Bool

instance : BEq Float := ⟨Float.beq⟩

@[extern c inline "#1 < #2"]   constant Float.decLt (a b : Float) : Decidable (a < b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLt a b

@[extern c inline "#1 <= #2"] constant Float.decLe (a b : Float) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨a⟩, ⟨b⟩ => floatSpec.decLe a b

instance floatDecLt (a b : Float) : Decidable (a < b) := Float.decLt a b
instance floatDecLe (a b : Float) : Decidable (a ≤ b) := Float.decLe a b

@[extern "lean_float_to_string"] constant Float.toString : Float → String

@[extern c inline "(uint8_t)#1"] constant Float.toUInt8 : Float → UInt8
@[extern c inline "(uint16_t)#1"] constant Float.toUInt16 : Float → UInt16
@[extern c inline "(uint32_t)#1"] constant Float.toUInt32 : Float → UInt32
@[extern c inline "(uint64_t)#1"] constant Float.toUInt64 : Float → UInt64
@[extern c inline "(size_t)#1"] constant Float.toUSize : Float → USize

instance : ToString Float where
  toString := Float.toString

instance : Repr Float where
  reprPrec n _ := Float.toString n

instance : ReprAtom Float  := ⟨⟩

abbrev Nat.toFloat (n : Nat) : Float :=
  Float.ofNat n

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

@[extern "lean_float_of_scientific"] constant Float.ofScientific (m : Nat) (s : Bool) (e : Nat) : Float

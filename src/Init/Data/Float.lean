/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Data.ToString

structure FloatSpec :=
(float : Type)
(val   : float)
(lt    : float → float → Prop)
(le    : float → float → Prop)
(decLt : DecidableRel lt)
(decLe : DecidableRel le)

-- Just show FloatSpec is inhabited.
constant floatSpec : FloatSpec := {
  float := Unit,
  val   := (),
  lt    := fun _ _ => True,
  le    := fun _ _ => True,
  decLt := fun _ _ => inferInstanceAs (Decidable True),
  decLe := fun _ _ => inferInstanceAs (Decidable True)
}

structure Float :=
(val : floatSpec.float)

instance : Inhabited Float := ⟨{ val := floatSpec.val }⟩

@[extern "lean_float_of_nat"] constant Float.ofNat : (@& Nat) → Float := arbitrary _
@[extern c inline "#1 + #2"]  constant Float.add : Float → Float → Float := arbitrary _
@[extern c inline "#1 - #2"]  constant Float.sub : Float → Float → Float := arbitrary _
@[extern c inline "#1 * #2"]  constant Float.mul : Float → Float → Float := arbitrary _
@[extern c inline "#1 / #2"]  constant Float.div : Float → Float → Float := arbitrary _

def Float.lt  : Float → Float → Prop :=
fun a b => match a, b with
| ⟨a⟩, ⟨b⟩ => floatSpec.lt a b

def Float.le  : Float → Float → Prop := fun a b => floatSpec.le a.val b.val

instance : HasZero Float   := ⟨Float.ofNat 0⟩
instance : HasOne Float    := ⟨Float.ofNat 1⟩
instance : HasOfNat Float  := ⟨Float.ofNat⟩
instance : HasAdd Float    := ⟨Float.add⟩
instance : HasSub Float    := ⟨Float.sub⟩
instance : HasMul Float    := ⟨Float.mul⟩
instance : HasDiv Float    := ⟨Float.div⟩
instance : HasLess Float   := ⟨Float.lt⟩
instance : HasLessEq Float := ⟨Float.le⟩

@[extern c inline "#1 == #2"] constant Float.beq (a b : Float) : Bool := arbitrary _

instance : HasBeq Float := ⟨Float.beq⟩

@[extern c inline "#1 < #2"]   constant Float.decLt (a b : Float) : Decidable (a < b) :=
match a, b with
| ⟨a⟩, ⟨b⟩ => floatSpec.decLt a b

@[extern c inline "#1 <= #2"] constant Float.decLe (a b : Float) : Decidable (a ≤ b) :=
match a, b with
| ⟨a⟩, ⟨b⟩ => floatSpec.decLe a b

instance floatDecLt (a b : Float) : Decidable (a < b) := Float.decLt a b
instance floatDecLe (a b : Float) : Decidable (a ≤ b) := Float.decLe a b

@[extern "lean_float_to_string"] constant Float.toString : Float → String := arbitrary _

instance : HasToString Float := ⟨Float.toString⟩

abbrev Nat.toFloat (n : Nat) : Float :=
Float.ofNat n

@[extern "sin"] constant Float.sin : Float → Float := arbitrary _
@[extern "cos"] constant Float.cos : Float → Float := arbitrary _
@[extern "tan"] constant Float.tan : Float → Float := arbitrary _
@[extern "asin"] constant Float.asin : Float → Float := arbitrary _
@[extern "acos"] constant Float.acos : Float → Float := arbitrary _
@[extern "atan"] constant Float.atan : Float → Float := arbitrary _
@[extern "atan2"] constant Float.atan2 : Float → Float → Float := arbitrary _
@[extern "sinh"] constant Float.sinh : Float → Float := arbitrary _
@[extern "cosh"] constant Float.cosh : Float → Float := arbitrary _
@[extern "tanh"] constant Float.tanh : Float → Float := arbitrary _
@[extern "asinh"] constant Float.asinh : Float → Float := arbitrary _
@[extern "acosh"] constant Float.acosh : Float → Float := arbitrary _
@[extern "atanh"] constant Float.atanh : Float → Float := arbitrary _
@[extern "exp"] constant Float.exp : Float → Float := arbitrary _
@[extern "exp2"] constant Float.exp2 : Float → Float := arbitrary _
@[extern "log"] constant Float.log : Float → Float := arbitrary _
@[extern "log2"] constant Float.log2 : Float → Float := arbitrary _
@[extern "log10"] constant Float.log10 : Float → Float := arbitrary _
@[extern "pow"] constant Float.pow : Float → Float → Float := arbitrary _
@[extern "sqrt"] constant Float.sqrt : Float → Float := arbitrary _
@[extern "cbrt"] constant Float.cbrt : Float → Float := arbitrary _

instance : HasPow Float Float := ⟨Float.pow⟩

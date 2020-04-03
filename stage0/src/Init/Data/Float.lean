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
(decEq : DecidableEq float)
(decLt : DecidableRel lt)
(decLe : DecidableRel le)

-- Just show FloatSpec is inhabited.
constant floatSpec : FloatSpec := {
  float := Unit,
  val   := (),
  lt    := fun _ _ => True,
  le    := fun _ _ => True,
  decEq := inferInstanceAs (DecidableEq Unit),
  decLt := fun _ _ => inferInstanceAs (Decidable True),
  decLe := fun _ _ => inferInstanceAs (Decidable True)
}

def Float : Type := floatSpec.float
instance : Inhabited Float := ⟨floatSpec.val⟩

/- @[extern "lean_float_of_nat"] -/ constant Float.ofNat : (@& Nat) → Float := arbitrary _
/- @[extern c inline "#1 + #2"] -/  constant Float.add : Float → Float → Float := arbitrary _
/- @[extern c inline "#1 - #2"] -/  constant Float.sub : Float → Float → Float := arbitrary _
/- @[extern c inline "#1 * #2"] -/  constant Float.mul : Float → Float → Float := arbitrary _
/- @[extern c inline "#1 / #2"] -/  constant Float.div : Float → Float → Float := arbitrary _

def Float.lt  : Float → Float → Prop := floatSpec.lt
def Float.le  : Float → Float → Prop := floatSpec.le

instance : HasZero Float   := ⟨Float.ofNat 0⟩
instance : HasOne Float    := ⟨Float.ofNat 1⟩
instance : HasOfNat Float  := ⟨Float.ofNat⟩
instance : HasAdd Float    := ⟨Float.add⟩
instance : HasSub Float    := ⟨Float.sub⟩
instance : HasMul Float    := ⟨Float.mul⟩
instance : HasDiv Float    := ⟨Float.div⟩
instance : HasLess Float   := ⟨Float.lt⟩
instance : HasLessEq Float := ⟨Float.le⟩

/- @[extern c inline "#1 == #2"] -/ constant Float.decEq (a b : Float) : Decidable (a = b) := floatSpec.decEq a b
/- @[extern c inline "#1 < #2"]  -/  constant Float.decLt (a b : Float) : Decidable (a < b) := floatSpec.decLt a b
/- @[extern c inline "#1 <= #2"] -/ constant Float.decLe (a b : Float) : Decidable (a ≤ b) := floatSpec.decLe a b

/- @[extern "lean_float_to_string"] -/ constant Float.toString : Float → String := arbitrary _

instance : HasToString Float := ⟨Float.toString⟩

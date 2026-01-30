/-!
Panic during evaluation
-/

inductive ItsTrue2 : Prop
  | mk

instance : Decidable ItsTrue2 :=
  have : Inhabited (Decidable ItsTrue2) := ⟨isTrue .mk⟩
  panic! "oh no"

example : ItsTrue2 := by native_decide

exit

inductive foo :=
| a | b

open foo

definition decidable_eq_foo [instance] : ∀ f₁ f₂ : foo, decidable (f₁ = f₂)
| a  a := by left; reflexivity
| a  b := by right; contradiction
| b  a := by right; contradiction
| b  b := by left; reflexivity

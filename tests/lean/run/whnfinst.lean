import logic
open decidable

definition decidable_bin_rel {A : Type} (R : A → A → Prop) := Πx y, decidable (R x y)

section
  parameter {A : Type}
  parameter (R : A → A → Prop)

  theorem tst1 (H : Πx y, decidable (R x y)) (a b c : A) : decidable (R a b ∧ R b a)

  theorem tst2 (H : decidable_bin_rel R) (a b c : A) : decidable (R a b ∧ R b a ∨ R b b) :=
  _
end

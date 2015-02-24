import logic
open decidable

definition decidable_bin_rel [reducible] {A : Type} (R : A → A → Prop) := Πx y, decidable (R x y)

section
  variable {A : Type}
  variable (R : A → A → Prop)

  theorem tst1 (H : Πx y, decidable (R x y)) (a b c : A) : decidable (R a b ∧ R b a)

  theorem tst2 (H : decidable_bin_rel R) (a b c : A) : decidable (R a b ∧ R b a ∨ R b b) :=
  _
end

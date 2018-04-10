open decidable

attribute [reducible]
definition decidable_bin_rel {A : Type} (R : A → A → Prop) := Πx y, decidable (R x y)

section
  variable {A : Type}
  variable (R : A → A → Prop)

  theorem tst1 (H : Πx y, decidable (R x y)) (a b c : A) : decidable (R a b ∧ R b a) :=
  by tactic.apply_instance

  theorem tst2 (H : decidable_bin_rel R) (a b c : A) : decidable (R a b ∧ R b a ∨ R b b) :=
  by tactic.apply_instance
end

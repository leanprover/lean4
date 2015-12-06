constants {A : Type} (P : A → Prop) (R : A → A → Prop)
definition H [forward] : ∀ a, (: P a :) → ∃ b, R a b := sorry
print H

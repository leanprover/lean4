constants {A : Type.{1}} (P : A → Prop) (Q : A → Prop)
definition H : ∀ a, (: P a :) → Exists Q := sorry

set_option blast.ematch true

example (a : A) : P a → Exists Q :=
by blast

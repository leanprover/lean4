import algebra.group

variables {A : Type} [group A]

inductive foo :=
mk₁ : ∀ (a : A), a * a = a → foo

print foo

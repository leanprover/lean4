import data.list

constants f : nat → nat → nat
constants a b : nat
axiom H2 : a = b
set_option pp.all true

#app_builder congr (eq.refl (f a)), H2

constants g : ∀ {A :Type}, A → A → A
variables A : Type
variables l₁ l₂ l₃: list A
variables H : l₂ = l₃

#app_builder congr (eq.refl (g l₁)), H
#app_builder congr_arg (g l₁), H

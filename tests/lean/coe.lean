import logic

set_option pp.notation false

inductive Functor :=
mk : (Π (A B : Type), A → B) → Functor

definition Functor.to_fun [coercion] (f : Functor) {A B : Type} : A → B :=
Functor.rec (λ f, f) f A B

constant f : Functor
check f (0:num) = (0:num)

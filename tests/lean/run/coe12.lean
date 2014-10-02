import data.nat
inductive foo (A B : Type) : Type :=
mk : (Π {C : Type}, A → C → B) → foo A B

definition to_fun [coercion] {A B : Type} (f : foo A B) : Π {C : Type}, A → C → B :=
foo.rec (λf, f) f

constant f : foo nat nat
constant a : nat
check f a true

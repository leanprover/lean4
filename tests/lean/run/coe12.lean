import data.nat
inductive foo (A B : Type) : Type :=
mk : (Π {C : Type}, A → C → B) → foo A B

definition to_fun [coercion] {A B : Type} (f : foo A B) : Π {C : Type}, A → C → B :=
foo.rec (λf, f) f

variable f : foo nat nat
variable a : nat
check f a true

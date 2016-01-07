import data.unit
open nat unit

constant r {A B : Type} : A → B → A

example (a b c d : unit) : r a b = r c d :=
by simp

example (a b : unit) : a = b :=
by simp

example (a b : unit) : (λ x : nat, a) = (λ y : nat, b) :=
by simp

example (a b : unit) : (λ x : nat, r a b) = (λ y : nat, r b b) :=
by simp

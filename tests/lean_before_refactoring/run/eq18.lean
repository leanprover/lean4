import data.examples.vector
open nat vector

definition last {A : Type} : Π {n}, vector A (succ n) → A
| last (a :: nil) := a
| last (a :: v)   := last v

theorem last_cons_nil {A : Type} {n : nat} (a : A) : last (a :: nil) = a :=
rfl

theorem last_cons {A : Type} {n : nat} (a : A) (v : vector A (succ n)) : last (a :: v) = last v :=
rfl

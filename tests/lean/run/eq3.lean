import data.examples.vector
open nat vector

definition swap {A : Type} : Π {n}, vector A (succ (succ n)) → vector A (succ (succ n))
| swap (a :: b :: vs) := b :: a :: vs

example (n : nat) (a b : num) (v : vector num n) : swap (a :: b :: v) = b :: a :: v :=
rfl

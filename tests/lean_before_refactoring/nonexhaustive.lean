import data.examples.vector
open nat vector

variable {A : Type}

definition foo : Π {n : nat}, vector A n → nat
| foo nil           := 0
| foo (a :: b :: v) := 0

set_option pp.implicit false

definition foo : Π {n : nat}, vector A n → nat
| foo nil           := 0
| foo (a :: b :: v) := 0

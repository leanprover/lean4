import data.examples.vector
open nat vector

set_option pp.implicit true
set_option pp.notation false

definition diag {A : Type} : Π {n}, vector (vector A n) n → vector A n,
diag nil               := nil,
diag ((a :: va) :: vs) := a :: diag (map tail vs)

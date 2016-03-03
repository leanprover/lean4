import data.examples.vector
open nat vector

definition diag {A : Type} : Π {n}, vector (vector A n) n → vector A n
| diag nil               := nil
| diag ((a :: va) :: vs) := a :: diag (map tail vs)

theorem diag_nil (A : Type) : diag (@nil (vector A 0)) = nil :=
rfl

theorem diag_succ {A : Type} {n : nat} (a : A) (va : vector A n) (vs : vector (vector A (succ n)) n) :
    diag ((a :: va) :: vs) = a :: diag (map tail vs) :=
rfl

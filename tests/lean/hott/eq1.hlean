open nat

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n}, A → vector A n → vector A (succ n)

infixr `::` := vector.cons

definition swap {A : Type} : Π {n}, vector A (succ (succ n)) → vector A (succ (succ n))
| swap (a :: b :: vs) := b :: a :: vs

-- Remark: in the current approach for HoTT, the equation
--    swap (a :: b :: v) = b :: a :: v
-- holds definitionally only when the index is a closed term.
example (a b : num) (v : vector num 5) : swap (a :: b :: v) = b :: a :: v :=
rfl

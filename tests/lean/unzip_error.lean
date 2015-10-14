import data.examples.vector
open nat vector prod

variables {A B : Type}

definition unzip : Π {n : nat}, vector (A × B) n → vector A n × vector B n
| unzip  nil          := (nil, nil)
| unzip ((a, b) :: v) :=
  match unzip v with -- ERROR
    (va, vb) := (a :: va, b :: vb)
  end

example : unzip ((1, 20) :: (2, 30) :: nil) = ((1 :: 2 :: nil, 20 :: 30 :: nil) : vector nat 2 × vector nat 2) :=
rfl

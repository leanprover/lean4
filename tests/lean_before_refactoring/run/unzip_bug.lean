import data.examples.vector
open nat vector prod

variables {A B : Type}

definition unzip : Π {n : nat}, vector (A × B) n → vector A n × vector B n
| @unzip ⌞zero⌟   nil           := (nil, nil)
| @unzip ⌞succ n⌟ ((a, b) :: v) :=
  match unzip v with
   (va, vb) := (a :: va, b :: vb)
  end

example : unzip ((1, 20) :: ((2, 30) : nat × nat) :: nil) = (1 :: 2 :: nil, 20 :: 30 :: nil) :=
rfl

example : List (Unit -> Nat) :=
  let g := [by exact fun _ => 0]; g

example : List (Unit -> Nat) :=
  let g := [fun _ => 0]; g

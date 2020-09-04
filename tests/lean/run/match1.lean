new_frontend

def f (xs : List Nat) : List Bool :=
xs.map fun
  | 0 => true
  | _ => false

#eval f [1, 2, 0, 2]

theorem ex1 : f [1, 0, 2] = [false, true, false] :=
rfl

#check f

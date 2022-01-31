@[simp] def f (x : Nat) : Nat :=
  match x with
  | 0    => 1
  | 100  => 2
  | 1000 => 3
  | x+1  => f x

#check f._eq_1
#check f._eq_2
#check f._eq_3
#check f._eq_4

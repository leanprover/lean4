@[simp] def g (x y : Nat) : Nat :=
  match x, y with
  | 0,   0 => 1
  | 0,   y => y
  | x+1, 5 => 2 * g x 0
  | x+1, y => 2 * g x y

#check g.eq_1
#check g.eq_2
#check g.eq_3
#check g.eq_4

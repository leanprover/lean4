@[simp] def g (x y : Nat) : Nat :=
  match x, y with
  | 0,   0 => 1
  | 0,   y => y
  | x+1, 5 => 2 * g x 0
  | x+1, y => 2 * g x y

/-- info: g.eq_1 : g 0 0 = 1 -/
#guard_msgs in
#check g.eq_1

/-- info: g.eq_2 (y : Nat) (x_2 : y = 0 → False) : g 0 y = y -/
#guard_msgs in
#check g.eq_2

/-- info: g.eq_3 (x_2 : Nat) : g x_2.succ 5 = 2 * g x_2 0 -/
#guard_msgs in
#check g.eq_3

/-- info: g.eq_4 (y x_2 : Nat) (x_3 : y = 5 → False) : g x_2.succ y = 2 * g x_2 y -/
#guard_msgs in
#check g.eq_4

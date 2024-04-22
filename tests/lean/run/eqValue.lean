@[simp] def f (x : Nat) : Nat :=
  match x with
  | 0    => 1
  | 100  => 2
  | 1000 => 3
  | x+1  => f x

/-- info: f.eq_1 : f 0 = 1 -/
#guard_msgs in
#check f.eq_1
/-- info: f.eq_2 : f 100 = 2 -/
#guard_msgs in
#check f.eq_2
/-- info: f.eq_3 : f 1000 = 3 -/
#guard_msgs in
#check f.eq_3
/--
info: f.eq_4 (x_2 : Nat) (x_3 : x_2 = 99 → False) (x_4 : x_2 = 999 → False) : f x_2.succ = f x_2
-/
#guard_msgs in
#check f.eq_4

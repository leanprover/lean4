def f (x : Nat) : Nat :=
  if h : x = 0 then
    1
  else
   f (x - 1) * 2
decreasing_by
  apply Nat.pred_lt
  exact h

/-- info: f.eq_1 (x : Nat) : f x = if h : x = 0 then 1 else f (x - 1) * 2 -/
#guard_msgs in
#check f.eq_1

/-- info: f.eq_def (x : Nat) : f x = if h : x = 0 then 1 else f (x - 1) * 2 -/
#guard_msgs in
#check f.eq_def

/-- error: unknown identifier 'f.eq_2' -/
#guard_msgs in
#check f.eq_2

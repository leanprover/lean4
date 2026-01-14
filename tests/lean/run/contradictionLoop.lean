theorem ex (h : 10000 = 100001) : False := by
  contradiction

/--
info: theorem ex : 10000 = 100001 → False :=
fun h => absurd h (of_decide_eq_false (Eq.refl (decide (10000 = 100001))))
-/
#guard_msgs in
#print ex

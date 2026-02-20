def f (x : Nat) :=
  let n := x + 1
  n + n

example : f x = 2*x + 2 := by
  dsimp [f]
  guard_target =ₛ x + 1 + (x + 1) = 2*x + 2
  simp +arith

def f (x : Nat) := x + 1

def g (x : Nat) := f x + f x

example : g x > 0 := by
  unfold g f
  simp +arith

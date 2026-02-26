def f (x y : Nat) : Nat :=
  match x, y with
  | 0, 0 => 1
  | _, _ => 2

example (h : f x y = 1) : f x y ≠ 2 := by
  simp [f] at *
  split
  next => decide
  next x' y' hnp => simp [hnp] at h

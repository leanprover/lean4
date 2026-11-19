example (x : Nat) (h : x = 2^1000 + 5) : x = 2^1000 + 5 := by
  grind

example (y : Nat) (f : Nat → Nat) (h : f (2^1000 + 5) = y) : f (2^1000 + 5) = y := by
  grind

example (a b : Nat) : 3 * a * b = a * b * 3 := by grind

example (k z : Nat) : k * (z * 2 * (z * 2 + 1)) = z * (k * (2 * (z * 2 + 1))) := by grind

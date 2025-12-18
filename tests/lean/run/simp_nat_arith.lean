example (x y : Nat) : (2*x + y = 4) ↔ (y + x + x = 4) := by
  simp +arith

example (x y : Nat) : (2*x + y ≤ 3) ↔ (y + x + x ≤ 3) := by
  simp +arith

example (f : Nat → Nat) (x y : Nat) : f (2*x + y) = f (y + x + x) := by
  simp +arith

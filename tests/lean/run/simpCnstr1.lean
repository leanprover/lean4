
example (a b : Nat) (h : a ≤ 2) : a + b + 1 + a < b + 4 + a := by
  simp +arith
  exact h

example (a b : Nat) (h : a = b + 3) : a + b + 1 + a = b + 4 + a + b := by
  simp +arith
  exact h

example (a b : Nat) (h : 1 = a + 2*b) : 5 = b + 4 + a + b := by
  simp +arith
  exact h

example (a : Nat) (h : 3 = a) : 4 = 1 + a := by
  simp +arith
  exact h

example (a b : Nat) (h : b ≤ 8) : 4 + ((a + a) + b) + (a + a) + (b + b) ≤ 3 + (4*a + b) + b + 8 + 1 := by
  simp +arith
  exact h

example (a : Nat) (h : False) : 4 = 8 + a := by
  simp +arith
  exact h

example (a b : Nat) : a + a ≤ 8 + a + a + b := by
  simp +arith

example (a b c d : Nat) (h : c + d ≤ a + b) : b + a + c + d ≤ a + b + a + b := by
  simp +arith
  exact h

example (a b : Nat) (h : 4 ≤ a) : a + b + 1 + a > b + 4 + a := by
  simp +arith
  exact h

example (a b : Nat) (h : 3 ≤ a) : a + b + 1 + a ≥ b + 4 + a := by
  simp +arith
  exact h

example (a b : Nat) (h : 3 ≤ a) : ¬ (a + b + 1 + a < b + 4 + a) := by
  simp +arith
  exact h

example (a b : Nat) (h : a ≤ 3) : ¬ (a + b + 1 + a > b + 4 + a) := by
  simp +arith
  exact h

example (a b : Nat) (h : 4 ≤ a) : ¬ (a + b + 1 + a ≤ b + 4 + a) := by
  simp +arith
  exact h

example (a b c d : Nat) (h : a + 2*d ≤ c + 2) : ¬ (a + d + b + 1 + a + d ≥ b + 4 + a + c) := by
  simp +arith
  exact h

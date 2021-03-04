theorem ex1 (n m : Nat) : 0 + (n, m).1 = n := by
  simp only
  rw [Nat.zero_add]

theorem ex2 (n m : Nat) : 0 + (n, m).1 = n := by
  simp

theorem ex3 (n m : Nat) : 0 + (n, m).1 + 0 = n := by
  simp only [Nat.add_zero]
  rw [Nat.zero_add]

theorem ex4 (n m : Nat) : 0 + (n, m).1 + 0 = n := by
  simp

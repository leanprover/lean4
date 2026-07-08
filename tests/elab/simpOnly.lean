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

theorem ex5 (m n : Nat) : m + n = n + m := by
  induction n with
  | zero      => rw [Nat.zero_add, Nat.add_zero]
  | succ n ih => simp only [Nat.add_succ, Nat.succ_add, ih]

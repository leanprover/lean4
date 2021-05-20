theorem ex (n : Nat) : True := by
  have : n = 0 + n := by rw [Nat.zero_add]
  skip
--^ $/lean/plainGoal
  exact True.intro

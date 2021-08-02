example : 0 * x = 0 := by simp
example : 1 * x = x := by simp
example : 2 * x = x + x := by simp [Nat.succ_mul]
example : 3 * x = x + x + x := by simp [Nat.succ_mul]

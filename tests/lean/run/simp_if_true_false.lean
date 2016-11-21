example (m n p : ℕ) : ite (m = m) n p = n := by simp
example (m n p : ℕ) : ite (m ≠ m) n p = p := by simp

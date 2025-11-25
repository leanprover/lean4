-- Catch special case of induction pattern that uses Mathlib's alternative `induction'` syntax,
-- which is used in the Natural Numbers game as just `induction`, overlapping with the parser for
-- Lean's default tactic

theorem zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with n n_ih
  rw [Nat.mul_zero]
  rw [Nat.mul_succ]
  rw [Nat.add_zero]
  rw [n_ih]

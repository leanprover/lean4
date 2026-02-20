class NeZero' (n : Nat) : Prop
theorem mul_div (m n : Nat) [NeZero' n] : (m * n) / n = m := sorry
example [NeZero' n] : (m * n) / n = m := by simp [mul_div m _]

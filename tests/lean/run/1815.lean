variable {α : Type _} [Mul α] [Inhabited α]

abbrev Left (a : α) : α := a * default
abbrev Right (a : α): α := default * a

theorem mul_comm (a b : α) : a * b = b * a := sorry

set_option trace.Meta.Tactic.simp true
example (a : α) : Left a = Right a := by
  simp [mul_comm]

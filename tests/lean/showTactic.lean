example : (∀ x, x = 0) ∧ (∀ x, x = 1) ∧ (∀ x, x = 2) ∧ (∀ x, x = 3) := by
  and_intros
  all_goals intro x
  show _ = 0 + 0
  trace_state
  show _ = 3
  trace_state
  show _ = 2
  show _ = 1
  show _ = 0
  trace_state
  show _ = 4

example : (∀ x, x = 0) ∧ (∀ y, y = 1) ∧ (∀ z, z = 2) ∧ (∀ a, a = 3) := by
  and_intros
  all_goals unhygienic intro
  show _ + 0 = 2
  trace_state
  show a = _
  trace_state
  show _ = 0
  trace_state
  show b = 3

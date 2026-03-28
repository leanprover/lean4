variable {P Q : Prop}

/--
error: Failed to find a hypothesis with type
  P ↔ Q
-/
#guard_msgs in
example : P ↔ Q := by
  rename P ↔ Q => goal
  obtain ⟨hpq, hqp⟩ := goal
  constructor <;> trivial

variable {P Q : Prop}

example : P ↔ Q := by
  rename P ↔ Q => goal
  obtain ⟨hpq, hqp⟩ := goal
  constructor <;> trivial

example : p → q → p ∧ q ∧ p := by
  intro hp hq
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

example : p → q → p ∧ q ∧ p := by
  intro hp hq
  apply And.intro
  exact hp
  exact And.intro hq hp

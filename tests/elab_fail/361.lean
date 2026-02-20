theorem ex1 (p q r : Prop) (h1 : p ∨ q) (h2 : p → q) : q := by

theorem ex2 (p q r : Prop) (h1 : p ∨ q) (h2 : p → q) : q := by
  cases h1
  case inl =>

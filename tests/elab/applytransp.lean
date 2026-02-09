theorem ex1 (h₁ : ¬ p) (h₂ : q → p) : ¬ q := by
  intro h
  apply h₁
  apply h₂
  apply h

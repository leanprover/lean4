set_option tactic.simp.trace true

example {P : Nat → Type} (h₁ : n = m) (h₂ : P m) : P n := by
  simp_all
  exact h₂

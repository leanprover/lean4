open List

set_option grind.warning false

variable {α} {l₁ l₂ l₃ l₄ l₅ : List α}

example : l₂ ++ l₄ ⊆ l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅ := by
  grind

example : l₂ ++ l₄ <+ l₁ ++ l₂ ++ l₃ ++ l₄ ++ l₅ := by
  grind

example : l₁ ++ l₂ <+: l₁ ++ (l₂ ++ l₃) := by
  grind

example : l₂ ++ l₃ <:+ l₁ ++ l₂ ++ l₃ := by
  grind

example : l₂ ++ l₃ <:+: l₁ ++ l₂ ++ l₃ ++ l₄ := by
  grind

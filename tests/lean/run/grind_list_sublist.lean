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

example (h : zs <+ ys) (w : xs ++ ys <+ zs) (h' : ¬xs = []) : False := by
  have : ∃ a ys, xs = a :: ys := sorry
  grind (gen := 6)

example {xs ys zs : List α} (h : zs <+ ys) :
    xs ++ ys <+ zs ↔ xs = [] ∧ ys = zs := by
  constructor
  · intro w
    grind
  · intro w
    grind

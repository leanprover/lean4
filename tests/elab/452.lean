example (h : x ∨ y) : y ∨ x := by
  cases h with
  | inl hx => first
    | apply Or.inr; assumption
    | apply Or.inl; assumption
  | inr hy => exact Or.inl hy


example (h : x ∨ y) : y ∨ x := by
  cases h with
  | inl hx => first
    | apply Or.inl; assumption
    | apply Or.inr; assumption
  | inr hy => exact Or.inl hy

set_option grind.warning false

example (a b c : Nat) : a = 0 → b = 0 → c ≥ a + b := by
  grind

example (a b c : Nat) : a + b = 0 → a ≤ b + c + a → a ≤ c := by
  grind

example (a b : Nat) (_ : 2*a + 3*b = 0) (_ : 2 ∣ 3*b + 1) : False := by
  grind

example (a b c : Nat) : a + 2*b = 0 → b + c + b = 0 → a = c := by
  grind

example (a : Nat) : a ≤ 2 → a ≠ 0 → a ≠ 1 → a ≠ 2 → False := by
  grind

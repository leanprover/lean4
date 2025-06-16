set_option grind.warning false

example (a b : Int) : min a b = 10 → a ≥ 10 := by
  grind

example (a b : Int) : min a b ≤ a := by
  grind

example (a b : Int) : min a b ≤ b := by
  grind

example (a b : Int) : min a b ≤ min b a := by
  grind

example (a b : Int) : max a (min a b) ≥ a := by
  grind

example (a b : Int) : max a (min a b) ≥ min b a := by
  grind

example (a b : Int) : max a (max a b) ≥ b := by
  grind

example (a b : Int) : max a (max a b) ≥ a := by
  grind

example (a : Int) : max a a = a := by
  grind

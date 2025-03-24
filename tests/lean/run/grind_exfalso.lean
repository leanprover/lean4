set_option grind.warning false

example (x : Nat) (h : x < 0) : Nat → Nat := by
  grind

example : False → Nat := by
  grind

example : (x : Nat) → x < 0 → Nat := by
  grind

example : (x : Nat) → x < 3 → x > 4 → Nat := by
  grind

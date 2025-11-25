module
example (x y : Nat) : (x : Int) - (y : Int) = 0 → x = y := by
  grind

example (x y : Nat) : (x : Int) - (y : Int) ≤ 0 → (x : Int) - (y : Int) ≥ 0 → x = y := by
  grind

example (x y : Nat) : (x : Int) = (y : Int) → x = y := by
  grind

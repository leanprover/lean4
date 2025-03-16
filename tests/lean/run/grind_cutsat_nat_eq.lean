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

example (x y : Nat) : x / 2 + y = 3 → x = 5 → y = 1 := by
  grind

example (x y : Nat) : x % 2 + y = 3 → x = 5 → y = 2 := by
  grind

example (x y : Nat) : x = y / 2 → y % 2 = 0 → y = 2*x := by
  grind

example (x : Nat) : x - 0 = x := by
  grind

example (x : Nat) : x - x = 0 := by
  grind

example (x y : Nat) : x ≤ y → x - y = 0 := by
  grind

example (x y z : Nat) : x ≤ y → x - z ≤ y - z := by
  grind

example (x y : Nat) : (x + y) - y = x := by
  grind

example (x y z : Nat) : (x + y) - (y + z) = x - z := by
  grind

example (x y : Nat) : x + y - x = y := by
  grind

example (x y : Nat) : (x - y) - y = x - 2*y := by
  grind

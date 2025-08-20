example (x y z w : Int) : z * x * y = 4 → x = z + w → z = 1 → w = 2 → False := by
  grind -ring

example (x y z w : Int) : y * z * x = 4 → x = z + w → z = 1 → w = 2 → False := by
  grind -ring

example (x y z w : Int) : x = z + w → z = 1 → w = 2 → z * x * y = 4 → False := by
  grind -ring

example (x y z : Int) : x = 3 → z = 1 → z * x * y = 4 → False := by
  grind -ring

example (x y z w : Int) : x = 1 → y = 2 → z = 3 → w = 4 → x * y * z * w = 24 := by
  grind -ring

example (x y z w : Int) : 1 ≤ x → x < 2 → y = 2 → z = 3 → w = 4 → x * y * z * w = 24 := by
  grind -ring

example (x y z w : Int) : x = 1 → y = 2 → z = 3 → w = 4 → x * (y * z) * w = 24 := by
  grind -ring

example (x y : Int) : 1 ≤ x → x ≤ 1 → 2 ≤ y → y ≤ 2 → x * y = 2 := by
  grind -ring

example (a : Nat) (ha : a < 8) (b : Nat) (hb : b = 2) : a * b < 8 * b := by
  grind

example (a : Nat) (ha : a < 8) (b c : Nat) : 2 ≤ b → c = 1 → b ≤ c + 1 → a * b < 8 * b := by
  grind

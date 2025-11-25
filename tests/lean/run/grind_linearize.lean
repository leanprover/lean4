module
example (x y z w : Int) : z * x * y = 4 → x = z + w → z = 1 → w = 2 → False := by
  grind -ring

example (x y z w : Int) : y * z * x = 4 → x = z + w → z = 1 → w = 2 → False := by
  grind -ring

example (x y z w : Int) : y * z * x * w = 4 → x = 0 → False := by
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
  grind -ring

example (a : Nat) (ha : a < 8) (b c : Nat) : 2 ≤ b → c = 1 → b ≤ c + 1 → a * b < 8 * b := by
  grind -ring

example (h : s = 4) : 4 < s - 1 + (s - 1) * (s - 1 - 1) / 2 := by
  grind

example (a b : Int) : a / b = 0 → b = 2 → a = 0 ∨ a = 1 := by
  grind

example (a b : Int) : b = 2 → a / b = 0 → a = 0 ∨ a = 1 := by
  grind

example (a b : Int) : b > 0 → b = 2 → a / b = 0 → a = 0 ∨ a = 1 := by
  grind

example (a b : Nat) : b > 0 → b = 2 → a / b = 0 → a = 0 ∨ a = 1 := by
  grind

example (a b c : Int) : a % b = 1 → b = 2 → a = 2 * c → False := by
  grind

example (a b c : Int) : b = 2 → a % b = 1 → a = 2 * c → False := by
  grind

example (a b c : Int) : b > 0 → b = 2 → a % b = 1 → a = 2 * c → False := by
  grind

example (a b c : Nat) : b > 0 → b = 2 → a % b = 1 → a = 2 * c → False := by
  grind

example (a b c d : Nat) : b > 0 → d = 1 → b = d + 1 → a % b = 1 → a = 2 * c → False := by
  grind

example (a b c d : Nat) : b > 1 → d = 1 → b ≤ d + 1 → a % b = 1 → a = 2 * c → False := by
  grind

example (b : Int) : 4 % b = 1 → b = 2 → False := by
  grind

example (b : Int) : b = 2 → 4 % b = 1 → False := by
  grind

example (b : Nat) : 4 % b = 1 → b = 2 → False := by
  grind

example (b : Int) : 4 / b = 1 → b = 2 → False := by
  grind

example (b : Nat) : 4 / b = 1 → b = 2 → False := by
  grind

example (b : Int) : 4 % b = 1 → b ≤ 2 → 2 ≤ b → False := by
  grind

example (b : Int) : b ≤ 2 → 2 ≤ b → 4 % b = 1 → False := by
  grind

example (b : Nat) : 4 % b = 1 → b ≤ 2 → 2 ≤ b → False := by
  grind

example (b : Int) : 4 / b = 1 → b ≤ 2 → 2 ≤ b → False := by
  grind

example (b : Nat) : 4 / b = 1 → b ≤ 2 → 2 ≤ b → False := by
  grind

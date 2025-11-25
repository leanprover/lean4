example (n : Nat) : n = 3 → 2 ^ n > 8 → False := by
  grind

example (n : Nat) : n = 2 → n ^ 3 > 8 → False := by
  grind

example (n : Int) : n = 2 → n ^ 3 > 8 → False := by
  grind

example (n : Nat) : 2 ^ n > 8 → 3 ≤ n → n ≤ 3 → False := by
  grind

example (n : Nat) : n ^ 3 > 8 → 2 ≤ n → n ≤ 2 → False := by
  grind

example (n : Nat) : n = 2 → 2 ^ (n+1) > 8 → False := by
  grind

example (n : Nat) : n = 2 → 2 ^ (n+1) = 8 := by
  grind

example (n : Nat) : n = 2 → 2 ^ (2*n) = 16 := by
  grind

example (n m : Nat) : n ≤ 2 → m ≤ n → m = 2 → 2 ^ (2*n) = 16 := by
  grind

example (a n : Nat) : a ^ n ≠ 8 → 3 ≤ n → n ≤ 3 → a = 2 → False := by
  grind

example (a b : Int) (n : Nat) : a ^ n ≠ 8 → 3 ≤ n → n ≤ 3 → a = b + 1 → 1 ≤ b → b ≤ 1 → False := by
  grind

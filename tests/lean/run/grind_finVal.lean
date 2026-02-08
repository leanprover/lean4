module
example (a b : Fin 2) (n : Nat) : n = 1 → ↑(a + b) ≠ n → a ≠ 0 → b = 0 → False := by
  grind -ring

example (m n : Nat) (i : Fin (m + n)) (hi : m ≤ ↑i) : ↑i - m < n := by
  grind

example {n : Nat} (m : Nat) (i : Fin n) ⦃j : Fin (n + m)⦄
    (this : ↑i + m ≤ ↑j) : ↑j - m < n := by
  grind

example {n : Nat} (i : Fin n) (j : Nat) (hj : j < ↑i) : j < n := by
  grind

example (a : Fin 2) : ↑a ≠ 0 → ↑a ≠ 1 → False := by
  grind -ring

example (a : Fin 2) : ↑a > 0 → ↑a ≠ 1 → False := by
  grind -ring

example (a : Fin 2) (b : Nat) : ↑a + b ≠ 0 → b = 0 → ↑a ≠ 1 → False := by
  grind -ring

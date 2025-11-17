open Lean Grind

example (a b : Nat) (h : a + b > 5) : (if a + b ≤ 2 then b else a) = a := by
  grind -linarith -lia (splits := 0)

example (a b c : Nat) : a ≤ b → b ≤ c → c < a → False := by
  grind -linarith -lia (splits := 0)

example (a b : Nat) : a ≤ 5 → b ≤ 8 → a > 6 ∨ b > 10 → False := by
  grind -linarith -lia (splits := 0)

example (a b c d : Nat) : a ≤ b → b ≤ c → c ≤ d → a ≤ d := by
  grind -linarith -lia (splits := 0)

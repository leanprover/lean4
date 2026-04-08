open Lean Grind Std

example [LE α] [IsPartialOrder α] (a b : α) (f : α → Nat) : a ≤ b → b ≤ c → c ≤ a → f a = f b := by
  grind (splits := 0)

example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPartialOrder α] [OrderedRing α]
    (a b : α) (f : α → Int) : a ≤ b + 1 → b ≤ a - 1 → f a = f (2 + b - 1) := by
  grind -mbtc -lia -linarith (splits := 0)

example (a b : Int) (f : Int → Int) : a ≤ b + 1 → b ≤ a - 1 → f a = f (2 + b - 1) := by
  grind -mbtc -lia -linarith (splits := 0)

example (a b : Nat) (f : Nat → Int) : a ≤ b + 1 → b + 1 ≤ a → f a = f (1 + b + 0) := by
  grind -mbtc -lia -linarith (splits := 0)

example (a b : Nat) (f : Nat → Int) : a ≤ b + 1 → b + 1 ≤ c → c ≤ a → f a = f c := by
  grind -mbtc -lia -linarith (splits := 0)

example (a b : Nat) (f : Nat → Int) : a ≤ b + 1 → b + 1 ≤ a → f (1 + a) = f (1 + b + 1) := by
  grind -mbtc -lia -linarith (splits := 0)

example
    : 2*n_1 + a = 1 → 2*n_1 + a = n_2 + 1 → n = 1 → n = n_3 + 1 → n_2 ≠ n_3 → False := by
  grind -lia -linarith -ring (splits := 0)

example
    : a = b → a ≤ b + 1 := by
  grind -lia -linarith -ring (splits := 0) only

example
    : a = b + 1 → a ≤ b + 2 := by
  grind -lia -linarith -ring (splits := 0) only

open Lean Grind Std

example [LE α] [IsPartialOrder α] (a b : α) (f : α → Nat) : a ≤ b → b ≤ c → c ≤ a → f a = f b := by
  grind (splits := 0)

example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPartialOrder α] [OrderedRing α]
    (a b : α) (f : α → Int) : a ≤ b + 1 → b ≤ a - 1 → f a = f (2 + b - 1) := by
  grind -mbtc -lia -linarith (splits := 0)

example (a b : Int) (f : Int → Int) : a ≤ b + 1 → b ≤ a - 1 → f a = f (2 + b - 1) := by
  grind -mbtc -lia -linarith (splits := 0)

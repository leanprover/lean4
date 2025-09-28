open Lean Grind

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α]
    (a b c d : α) : a ≤ b → ¬ (c ≤ b) → ¬ (d ≤ c) → d < a → False := by
  grind -linarith (splits := 0)

example [LE α] [Std.IsLinearPreorder α]
    (a b c d : α) : a ≤ b → ¬ (c ≤ b) → ¬ (d ≤ c) → ¬ (a ≤ d) → False := by
  grind -linarith (splits := 0)

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] [CommRing α] [OrderedRing α]
    (a b c d : α) : a - b ≤ 5 → ¬ (c ≤ b) → ¬ (d ≤ c + 2) → d ≤ a - 8 → False := by
  grind -linarith (splits := 0)

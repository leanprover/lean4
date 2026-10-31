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

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsLinearPreorder α] [CommRing α] [OrderedRing α]
    (a b c d : α) : a - b ≤ 5 → ¬ (c < b) → ¬ (d ≤ c + 2) → d ≤ a - 8 → False := by
  grind -linarith (splits := 0)

example (p : Prop) (a b c : Int) : (p ↔ b ≤ a) → (p ↔ c ≤ b) → ¬ p → c ≤ a + 1 → False := by
  grind -linarith -lia (splits := 0)

/--
error: `grind` has failed, use `+verbose` to obtain diagnostic information
-/
#guard_msgs in
example [LE α] [Std.IsPreorder α]
    (a b c : α) : a ≤ b → b ≤ c → c ≤ a → a = c := by
  grind -linarith -verbose

example [LE α] [Std.IsPartialOrder α]
    (a b c : α) : a ≤ b → b ≤ c → c ≤ a → a = c := by
  grind -linarith -verbose

example [LE α] [Std.IsLinearPreorder α]
    (a b c d e : α) : a ≤ b → b = c → d = c → d ≤ e → a ≤ e := by
  grind -linarith (splits := 0)

example [LE α] [Std.IsLinearPreorder α]
    (a b c d e : α) : a ≥ b → d = c → c = b → d ≥ e → a ≥ e := by
  grind -linarith (splits := 0)

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [CommRing α] [OrderedRing α]
    (a b c d e : α) : a ≥ b → d = c → c = b → d ≥ e → a ≥ e := by
  grind -linarith (splits := 0)

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [CommRing α] [OrderedRing α]
    (a b c d e : α) : a + 2 ≥ b → d = c → c = b → d + 1 ≥ e → a + 3 ≥ e := by
  grind -linarith (splits := 0)

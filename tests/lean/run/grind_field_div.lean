open Lean Grind

example [Field α] [IsCharP α 0] (a b c : α) : a/3 = b → c = a/3 → a/2 + a/2 = b + 2*c  := by
  grind

example [Field α] (a b : α) : b = 0 → (a + a) / 0 = b := by
  grind

example [Field α] [IsCharP α 3] (a b : α) : a/3 = b → b = 0 := by
  grind

example [Field α] [IsCharP α 7] (a b c : α) : a/3 = b → c = a/3 → a/2 + a/2 = b + 2*c + 7 := by
  grind

example [Field R] [IsCharP R 0] (x : R) (cos : R → R) :
    (cos x ^ 2 + (2 * cos x ^ 2 - 1) ^ 2 + (4 * cos x ^ 3 - 3 * cos x) ^ 2 - 1) / 4 =
      cos x * (cos x ^ 2 - 1 / 2) * (4 * cos x ^ 3 - 3 * cos x) := by
  grind

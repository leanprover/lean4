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

example [Field α] (a : α) : (1 / 2) * a = a / 2 := by grind

example [Field α] (a : α) : 2⁻¹ * a = a / 2 := by grind

example [Field α] (a : α) : a⁻¹⁻¹ = a := by grind

example [Field α] [IsCharP α 0] (a : α) : a / 2 + a / 3 = 5 * a / 6 := by
  grind

example [Field α] (a b : α) : a ≠ 0 → b ≠ 0 → a / (a / b) = b := by
  grind

example [Field α] (a b : α) : a ≠ 0 → a / (a / b) = b := by
  grind

example [Field α] [IsCharP α 0] (x : α)
    : x ≠ 0 → (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by
  grind

example [Field α] (a : α) : 2 * a ≠ 0 → 1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind

example [Field α] [IsCharP α 0] (a : α) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind

example [Field α] [IsCharP α 0] (a b : α) : 2*b - a = a + b → 1 / a + 1 / (2 * a) = 3 / b := by
  grind

example [Field α] [NoNatZeroDivisors α] (a : α) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind

example [Field α] {x y z w : α} : x / y = z / w → y ≠ 0 → w ≠ 0 → x * w = z * y := by
  grind

example [Field α] (a : α) : a = 0 → a ≠ 1 := by
  grind

example [Field α] (a : α) : a = 0 → a ≠ 1 - a := by
  grind

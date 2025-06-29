open Lean Grind

section CommSemiring

variable (R : Type u) [CommSemiring R]

example (a b c : R) : a * (b + c) = a * c + b * a := by grind
example (a b : R) : (a + b)^2 = a^2 + 2 * a * b + b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 4 * a * b + 4 * b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = 4 * b^2 + b * 4 * a + a^2 := by grind

example (a b : R) : (a + b)^2 ≠ a^2 + 2 * a * b + b^2 → False := by grind

end CommSemiring

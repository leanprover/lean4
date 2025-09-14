open Lean Grind

variable (R : Type u) [Ring R]
example (a b c : R) : a * (b - c) = - a * c + a * b := by grind
example (a b : R) : (a - b)^2 = a^2 - a * b - b * a + b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + -b * (-2) * a + 4 * b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + -b * (-4) * a - 2*b*a + 4 * b^2 := by grind

variable [IsCharP R 4]
example (a b : R) : (a - b)^2 = a^2 - a * b - b * 5 * a + b^2 := by grind
example (a b : R) : (a - b)^2 = 13*a^2 - a * b - b * 5 * a + b*3*b*3 := by grind

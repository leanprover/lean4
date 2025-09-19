open Lean.Grind

variable (R : Type u) [Semiring R]

example (a b c : R) : a * (b + c) = a * c + a * b := by grind
example (a b : R) : (a + b)^2 = a^2 + a * b + b * a + b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + b * 2 * a + 4 * b^2 := by grind
example (a b : R) : b^2 + (a + 2 * b)^2 = a^2 + 2 * a * b + b * 2 * a + 5 * b^2 := by grind
example (a b : R) : b^2 + (a + 2 * b)^2 = a^2 + 2 * a * b + b * (1+1) * a * 1 + 5 * b^2 := by grind
example (a b : R) : a^3 + a^2*b + a*b*a + b*a^2 + a*b^2 + b*a*b + b^2*a + b^3 = (a+b)^3 := by grind

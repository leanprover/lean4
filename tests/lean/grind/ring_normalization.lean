-- Tests for `grind` as a ring normalization tactic, when only `Semiring`, `CommSemiring`, or `Ring` is available.
-- Note that in these cases we *do not* support hypotheses: there's no (good) analogue of Grobner bases here.

open Lean.Grind

section Semiring

variable (R : Type u) [Semiring R]

example (a b c : R) : a * (b + c) = a * c + a * b := by grind
example (a b : R) : (a + b)^2 = a^2 + a * b + b * a + b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + 2 * b * a + 4 * b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 2 * a * b + b * 2 * a + 4 * b^2 := by grind

end Semiring

section CommSemiring

variable (R : Type u) [Semiring R]

example (a b c : R) : a * (b + c) = a * c + b * a := by grind
example (a b : R) : (a + b)^2 = a^2 + 2 * a * b + b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 + 4 * a * b + 4 * b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = 4 * b^2 + b * 4 * a + a^2 := by grind

end CommSemiring

section Ring

variable (R : Type u) [Ring R]

example (a b c : R) : a * (b - c) = - a * c + a * b := by grind
example (a b : R) : (a - b)^2 = a^2 - a * b - b * a + b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 - 2 * a * b - 2 * b * a + 4 * b^2 := by grind
example (a b : R) : (a + 2 * b)^2 = a^2 - 2 * a * b + -b * (-2) * -a + 4 * b^2 := by grind

end Ring

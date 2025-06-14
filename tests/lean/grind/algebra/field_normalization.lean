open Lean.Grind

variable (R : Type u) [Field R]

example (a : R) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind

example (a : R) (_ : (2 : R) ≠ 0) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind

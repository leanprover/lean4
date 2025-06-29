open Lean.Grind
set_option grind.debug true

variable (R : Type u) [Field R]

example (a : R) : (1 / 2) * a = a / 2 := by grind
example (a : R) : 2⁻¹ * a = a / 2 := by grind
example (a : R) : a⁻¹⁻¹ = a := by grind

example [IsCharP R 0] (a : R) : a / 2 + a / 3 = 5 * a / 6 := by grind

example {x z w y : R} (_ : x ≠ 0) (_ : z ≠ 0) : w / x + y / z = (w * z + y * x) / (x * z) := by grind
example {x z w y : R} (_ : x * z ≠ 0) : w / x + y / z = (w * z + y * x) / (x * z) := by grind

example {x y z w : R} (h : x / y = z / w) (hy : y ≠ 0) (hw : w ≠ 0) : x * w = z * y := by
  grind

example (a : R) (_ : 2 * a ≠ 0) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind
example [IsCharP R 0] (a : R) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind
example [NoNatZeroDivisors R] (a : R) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind

example (a b : R) (_ : a ≠ 0) (_ : b ≠ 0) : a / (a / b) = b := by grind
example (a b : R) (_ : a ≠ 0) : a / (a / b) = b := by grind

-- TODO: create a mock implementation of `ℚ` for testing purposes.
variable (ℚ : Type) [Field ℚ] [IsCharP ℚ 0]

example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by grind

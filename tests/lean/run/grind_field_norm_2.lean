open Lean.Grind

variable (R : Type u) [Field R]

example (a : R) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind

example (a : R) (_ : (2 : R) ≠ 0) : 1 / a + 1 / (2 * a) = 3 / (2 * a) := by grind

example [CommRing α] (a b : α) (h₁ : a + 2 = a) (h₂ : 2*b + a = 0) : a = 0 := by
  grind

example [CommRing α] (a b : α) (h₁ : a + 6 = a) (h₂ : b + 9 = b) (h₂ : 3*b + a = 0) : a = 0 := by
  grind

example [CommRing α] (a b : α) (h₁ : a + 6 = a) (h₂ : b + 9 = b) (h₂ : 3*b + a = 0) : a = 0 := by
  grind

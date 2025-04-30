open Lean.Grind

-- Then example in this file is failing with kernel deep recursion.

-- This one shouldn't succeed (it's true, but not over an arbitrary ring), but hopefully should fail cleanly.
example {α} [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α)
  (Δ40 : d^2 * (d + t - d * t - 2) *
    (d + t + d * t) = 0)
  (Δ41 : -d^4 * (d + t - d * t - 2) *
    (2 * d + 2 * d * t - 4 * d * t^2 + 2 * d * t^4 + 2 * d^2 * t^4 - c * (d + t + d * t)) = 0)
  (_ : d * d_inv = 1)
  (_ : (d + t - d * t - 2) * PSO3_inv = 1) :
  t^2 = t + 1 := by grind +ring -- (kernel) deep recursion detected

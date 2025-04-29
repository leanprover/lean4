open Lean.Grind

-- These are variants of the calculation in `grind_ring_3.lean`, but using `NoZeroNatDivisors`,
-- and which currently fail because of a kernel type mismatch.

-- Then final example in this file is failing with kernel deep recursion.

set_option grind.warning false

example {α} [CommRing α] [IsCharP α 0] [NoZeroNatDivisors α]
    (d t : α)
  (Δ40 : d + t + d * t = 0)
  (Δ41 : 2 * d + 2 * d * t - 4 * d * t^2 + 2 * d * t^4 + 2 * d^2 * t^4 = 0) :
  t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind +ring -- (kernel) application type mismatch

example {α} [CommRing α] [IsCharP α 0] [NoZeroNatDivisors α]
    (d t d_inv : α)
  (Δ40 : d * (d + t + d * t) = 0)
  (Δ41 : d^2 * (d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4) = 0)
  (_ : d * d_inv = 1) :
  t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind +ring -- (kernel) application type mismatch

-- This one shouldn't succeed (it's true, but not over an arbitrary ring), but hopefully should fail cleanly.
example {α} [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α)
  (Δ40 : d^2 * (d + t - d * t - 2) *
    (d + t + d * t) = 0)
  (Δ41 : -d^4 * (d + t - d * t - 2) *
    (2 * d + 2 * d * t - 4 * d * t^2 + 2 * d * t^4 + 2 * d^2 * t^4 - c * (d + t + d * t)) = 0)
  (_ : d * d_inv = 1)
  (_ : (d + t - d * t - 2) * PSO3_inv = 1) :
  t^2 = t + 1 := by grind +ring -- (kernel) deep recursion detected

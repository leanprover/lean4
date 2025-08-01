-- Do we want instances for products and function types, and ...?

example (p q : UInt8 × UInt8) : p - (p + q) + q = 0 := by
  grind

open Lean.Grind
example {α} [CommRing α] (p q : Nat → α) : p * q = q * p := by grind

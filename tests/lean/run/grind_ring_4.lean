module
open Lean.Grind

example {α} [CommRing α] [IsCharP α 0] [NoNatZeroDivisors α]
    (d t : α)
  (Δ40 : d + t + d * t = 0)
  (Δ41 : 2 * d + 2 * d * t - 4 * d * t^2 + 2 * d * t^4 + 2 * d^2 * t^4 = 0) :
  t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by
  grind

example {α} [CommRing α] [IsCharP α 0] [NoNatZeroDivisors α]
    (d t d_inv : α)
  (Δ40 : d * (d + t + d * t) = 0)
  (Δ41 : d^2 * (d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4) = 0)
  (_ : d * d_inv = 1) :
  t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by
  grind

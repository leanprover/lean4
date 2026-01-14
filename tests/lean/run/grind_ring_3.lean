module
open Lean.Grind

example {α} [CommRing α] [IsCharP α 0]
    (d t : α)
  (Δ40 : d + t + d * t = 0)
  (Δ41 : d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4 = 0) :
  t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind

example {α} [CommRing α] [IsCharP α 0]
    (d t d_inv : α)
  (Δ40 : d * (d + t + d * t) = 0)
  (Δ41 : d * (d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4) = 0)
  (_ : d * d_inv = 1) :
  t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind

-- The theorems above hold in any `CommRing`

example {α} [CommRing α]
    (d t : α)
  (Δ40 : d + t + d * t = 0)
  (Δ41 : d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4 = 0) :
  t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind

example {α} [CommRing α]
    (d t d_inv : α)
  (Δ40 : d * (d + t + d * t) = 0)
  (Δ41 : d * (d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4) = 0)
  (_ : d * d_inv = 1) :
  t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind

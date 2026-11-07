/-!
Benchmarks for the kernel checking of the `grind` ring solver's certificates in rings with a
nonzero characteristic (the `C` variants of `Lean.Grind.CommRing.Stepwise`).
-/

open Lean.Grind

example [CommRing α] [IsCharP α 7] (x y : α) : (x + y)^7 = x^7 + y^7 := by grind

example [CommRing α] [IsCharP α 11] (x y z : α) : (x + y + z)^11 = x^11 + y^11 + z^11 := by grind

example (x y : Fin 11) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by grind

example (x : Fin 19) : (1 + x) ^ 5 = x ^ 5 + 5 * x ^ 4 + 10 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1 := by grind

example (x y z : Fin 13) :
    (x + y + z) ^ 4 = x^4 + y^4 + z^4 + 4*(x^3*y + x^3*z + y^3*x + y^3*z + z^3*x + z^3*y)
      + 6*(x^2*y^2 + x^2*z^2 + y^2*z^2) + 12*(x^2*y*z + x*y^2*z + x*y*z^2) := by grind

example (x y : UInt8) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by grind

example (x y : BitVec 16) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by grind

example (x y z : BitVec 8) : z = y → (x + 1)*(x - 1)*y + y = z*x^2 + 1 → False := by grind

example (x y : BitVec 32) : (x - y) * (x^3 + x^2*y + x*y^2 + y^3) = x^4 - y^4 := by grind

example {α} [CommRing α] [IsCharP α 7] (d t : α)
    (Δ40 : d + t + d * t = 0)
    (Δ41 : d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4 = 0) :
    t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind

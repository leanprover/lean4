/-!
Benchmarks for the kernel checking of the `grind` ring solver's certificates
(`Lean.Grind.CommRing.Stepwise`): Gröbner basis problems over commutative rings of
characteristic zero.
-/

open Lean.Grind

example {α} [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α)
    (Δ40 : d^2 * (d + t - d * t - 2) * (d + t + d * t) = 0)
    (Δ41 : -d^4 * (d + t - d * t - 2) *
      (2 * d + 2 * d * t - 4 * d * t^2 + 2 * d * t^4 + 2 * d^2 * t^4 - c * (d + t + d * t)) = 0)
    (_ : d * d_inv = 1)
    (_ : (d + t - d * t - 2) * PSO3_inv = 1) :
    t^2 = t + 1 := by grind

example {α} [CommRing α] (d t : α)
    (Δ40 : d + t + d * t = 0)
    (Δ41 : d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4 = 0) :
    t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind

example {α} [CommRing α] (d t d_inv : α)
    (Δ40 : d * (d + t + d * t) = 0)
    (Δ41 : d * (d + d * t - 2 * d * t^2 + d * t^4 + d^2 * t^4) = 0)
    (_ : d * d_inv = 1) :
    t + 2 * t^2 - t^3 - 2 * t^4 + t^5 = 0 := by grind

-- Newton's identities for power sums
example [CommRing α] [NoNatZeroDivisors α] (a b c : α) :
    a + b + c = 3 → a^2 + b^2 + c^2 = 5 → a^3 + b^3 + c^3 = 7 → a^4 + b^4 + c^4 = 9 := by grind

example [CommRing α] [NoNatZeroDivisors α] (a b c : α) :
    a + b + c = 3 → a^2 + b^2 + c^2 = 5 → a^3 + b^3 + c^3 = 7 → 3 * (a^5 + b^5 + c^5) = 29 := by grind

example [CommRing α] [NoNatZeroDivisors α] (a b c d : α) :
    a + b + c + d = 1 → a^2 + b^2 + c^2 + d^2 = -3 → a^3 + b^3 + c^3 + d^3 = 4 →
    a^4 + b^4 + c^4 + d^4 = -3 → a^5 + b^5 + c^5 + d^5 = -24 := by grind

example (a b c : Int) :
    a + b + c = 3 → a^2 + b^2 + c^2 = 5 → a^3 + b^3 + c^3 = 7 → a^4 + b^4 + c^4 = 9 := by grind

example [CommRing α] (x y : α) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by grind

example [CommRing α] (x y : α) : x*y*x = 1 → x*y*y = y → y = 1 := by grind

example [Field α] [IsCharP α 0] (x y z : α) :
    x^2 + y^2 + z^2 = 1 → x + y + z = 1 → x*y + y*z + z*x = 0 := by grind

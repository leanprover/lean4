set_option grind.warning false
open Lean.Grind

example [CommRing α] [NoZeroNatDivisors α] (x y : α) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
  grind +ring

example [CommRing α] (x y : α) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
  fail_if_success grind +ring
  sorry

example [CommRing α] (x y : α) : x = 1 → y = 2 → 2*x + y = 4 := by
  grind +ring

example [CommRing α] [IsCharP α 7] (x y : α) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
  grind +ring

example [CommRing α] [IsCharP α 7] (x y : α) : 2*x = 1 → 2*y = 1 → x + y = 1 := by
  grind +ring

example [CommRing α] [IsCharP α 8] (x y : α) : 2*x = 1 → 2*y = 1 → x + y = 1 := by
  fail_if_success grind +ring
  sorry

example [CommRing α] [IsCharP α 8] [NoZeroNatDivisors α] (x y : α) : 2*x = 1 → 2*y = 1 → x + y = 1 := by
  grind +ring

example (x y : UInt8) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
  grind +ring

example (x y : UInt8) : 3*x = 1 → 3*y = 2 → False := by
  fail_if_success grind +ring
  sorry

example [CommRing α] [NoZeroNatDivisors α] (x y : α) : 6*x = 1 → 3*y = 2 → 2*x + y = 1 := by
  grind +ring

example [CommRing α] [NoZeroNatDivisors α] (x y : α) : 600000*x = 1 → 300*y = 2 → 200000*x + 100*y = 1 := by
  grind +ring

example (x y : Int) : y = 0 → (x + 1)*(x - 1) + y = x^2 → False := by
  grind +ring

example (x y z : BitVec 8) : z = y → (x + 1)*(x - 1)*y + y = z*x^2 + 1 → False := by
  grind +ring

example [CommRing α] (x y : α) : x*y*x = 1 → x*y*y = y → y = 1 := by
  grind +ring

example [CommRing α] (x y : α) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind +ring

example (x y : BitVec 16) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind +ring

example [CommRing α] (x y : α) (f : α → Nat) : x^2*y = 1 → x*y^2 = y → f (y*x) = f 1 := by
  grind +ring

example [CommRing α] (x y : α) (f : α → Nat) : x^2*y = 1 → x*y^2 - y = 0 → f (y*x) = f (y*x*y) := by
  grind +ring

example [CommRing α] (a b c : α)
  : a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    a^4 + b^4 + c^4 = 9 := by
  grind +ring

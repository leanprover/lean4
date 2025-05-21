set_option grind.warning false
set_option grind.debug true
open Lean.Grind

example [CommRing α] [NoNatZeroDivisors α] (x y : α) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
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

example [CommRing α] [IsCharP α 8] [NoNatZeroDivisors α] (x y : α) : 2*x = 1 → 2*y = 1 → x + y = 1 := by
  grind +ring

example (x y : UInt8) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
  grind +ring

example (x y : UInt8) : 3*x = 1 → 3*y = 2 → False := by
  fail_if_success grind +ring
  sorry

example [CommRing α] [NoNatZeroDivisors α] (x y : α) : 6*x = 1 → 3*y = 2 → 2*x + y = 1 := by
  grind +ring

example [CommRing α] [NoNatZeroDivisors α] (x y : α) : 600000*x = 1 → 300*y = 2 → 200000*x + 100*y = 1 := by
  grind +ring

example (x y : Int) : y = 0 → (x + 1)*(x - 1) + y = x^2 → False := by
  grind +ring

example (x y : Int) : y = 0 → (x + 1)*(x - 1) + y = x^2 → False := by
  grind +ringNull

example (x y z : BitVec 8) : z = y → (x + 1)*(x - 1)*y + y = z*x^2 + 1 → False := by
  grind +ring

example (x y z : BitVec 8) : z = y → (x + 1)*(x - 1)*y + y = z*x^2 + 1 → False := by
  grind +ringNull

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

/--
trace: [grind.ring.assert.basis] a + b + c + -3 = 0
[grind.ring.assert.basis] 2 * b ^ 2 + 2 * (b * c) + 2 * c ^ 2 + -6 * b + -6 * c + 4 = 0
[grind.ring.assert.basis] 6 * c ^ 3 + -18 * c ^ 2 + 12 * c + 4 = 0
-/
#guard_msgs (trace) in
example [CommRing α] (a b c : α)
  : a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    a^4 + b^4 = 9 - c^4 := by
  set_option trace.grind.ring.assert.basis true in
  grind +ring

/--
trace: [grind.ring.assert.basis] a + b + c + -3 = 0
[grind.ring.assert.basis] b ^ 2 + b * c + c ^ 2 + -3 * b + -3 * c + 2 = 0
[grind.ring.assert.basis] 3 * c ^ 3 + -9 * c ^ 2 + 6 * c + 2 = 0
-/
#guard_msgs (trace) in
example [CommRing α] [NoNatZeroDivisors α] (a b c : α)
  : a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    a^4 + b^4 = 9 - c^4 := by
  set_option trace.grind.ring.assert.basis true in
  grind +ring

example [CommRing α] (a b : α) (f : α → Nat) : a - b = 0 → f a = f b := by
  grind +ring

example (a b : BitVec 8) (f : BitVec 8 → Nat) : a - b = 0 → f a = f b := by
  grind +ring

example (a b c : BitVec 8) (f : BitVec 8 → Nat) : c = 255 → - a + b - 1 = c → f a = f b := by
  grind +ring

example (a b c : BitVec 8) (f : BitVec 8 → Nat) : c = 255 → - a + b - 1 = c → f (2*a) = f (b + a) := by
  grind +ring

/-- trace: [grind.ring.impEq] skip: b = a, k: 2, noZeroDivisors: false -/
#guard_msgs (trace) in
example (a b c : BitVec 8) (f : BitVec 8 → Nat) : 2*a = 1 → 2*b = 1 → f (a) = f (b) := by
  set_option trace.grind.ring.impEq true in
  fail_if_success grind +ring
  sorry

example (a b c : Int) (f : Int → Nat)
  : a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    f (a^4 + b^4) + f (9 - c^4) ≠ 1 := by
  grind +ring

example [CommRing α] (a b c : α) (f : α → Nat)
  : a + b + c = 3 →
    a^2 + b^2 + c^2 = 5 →
    a^3 + b^3 + c^3 = 7 →
    f (a^4 + b^4) + f (9 - c^4) ≠ 1 := by
  grind +ring

example [CommRing α] [NoNatZeroDivisors α] (x y z : α) : 3*x = 1 → 3*z = 2 → 2*y = 2 → x + z + 3*y = 4 := by
  grind +ring

example (x y : Fin 11) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind +ring

example (x y : Fin 11) : 3*x = 1 → 3*y = 2 → x + y = 1 := by
  grind +ring

example (x y z : Fin 13) :
    (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
  grind +ring

example (x y : Fin 17) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * x * y * (x + y) := by
  grind +ring

example (x y : Fin 19) : (x - y) * (x ^ 2 + x * y + y ^ 2) = x ^ 3 - y ^ 3 := by
  grind +ring

example (x : Fin 19) : (1 + x) ^ 5 = x ^ 5 + 5 * x ^ 4 + 10 * x ^ 3 + 10 * x ^ 2 + 5 * x + 1 := by
  grind +ring

example (x : Fin 10) : (1 + x) ^ 5 = x ^ 5 + 5 * x ^ 4 - 5 * x + 1 := by
  grind +ring

example (x y : Fin 3) (h : x = y) : ((x + y) ^ 3 : Fin 3) = - x^3 := by grind +ring

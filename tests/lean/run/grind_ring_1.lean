set_option grind.warning false
set_option grind.debug true

open Lean.Grind

example [CommRing α] (x : α) : (x + 1)*(x - 1) = x^2 - 1 := by
  grind +ring

example [CommRing α] [IsCharP α 256] (x : α) : (x + 16)*(x - 16) = x^2 := by
  grind +ring

example (x : Int) : (x + 1)*(x - 1) = x^2 - 1 := by
  grind +ring

example (x : UInt8) : (x + 16)*(x - 16) = x^2 := by
  grind +ring

/--
trace: [grind.ring] new ring: Int
[grind.ring] characteristic: 0
[grind.ring] NoNatZeroDivisors available: true
-/
#guard_msgs (trace) in
set_option trace.grind.ring true in
example (x : Int) : (x + 1)^2 - 1 = x^2 + 2*x := by
  grind +ring

example (x : BitVec 8) : (x + 16)*(x - 16) = x^2 := by
  grind +ring

/--
trace: [grind.ring] new ring: BitVec 8
[grind.ring] characteristic: 256
[grind.ring] NoNatZeroDivisors available: false
-/
#guard_msgs (trace) in
set_option trace.grind.ring true in
example (x : BitVec 8) : (x + 1)^2 - 1 = x^2 + 2*x := by
  grind +ring

example (x : Int) : (x + 1)*(x - 1) = x^2 → False := by
  grind +ring

example (x y : Int) : (x + 1)*(x - 1)*y + y = y*x^2 + 1 → False := by
  grind +ring

example (x : UInt8) : (x + 1)*(x - 1) = x^2 → False := by
  grind +ring

example (x y : BitVec 8) : (x + 1)*(x - 1)*y + y = y*x^2 + 1 → False := by
  grind +ring

example [CommRing α] (x : α) : (x + 1)*(x - 1) = x^2 → False := by
  fail_if_success grind +ring
  sorry

example [CommRing α] [IsCharP α 0] (x : α) : (x + 1)*(x - 1) = x^2 → False := by
  grind +ring

example [CommRing α] [IsCharP α 8] (x : α) : (x + 1)*(x - 1) = x^2 → False := by
  grind +ring

/-- trace: [grind.ring.assert.queue] -7 * x ^ 2 + 16 * y ^ 2 + x = 0 -/
#guard_msgs (trace) in
set_option trace.grind.ring.assert.queue true in
example (x y : Int) : x + 16*y^2 - 7*x^2 = 0 → False := by
  fail_if_success grind +ring
  sorry

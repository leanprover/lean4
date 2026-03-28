module
example (n t : Nat) : 1 ^ (n / 3) * 2 ^ t = 2 ^ t := by grind

example (n t : Nat) : (1 : Int) ^ (n / 3) * 2 ^ t = 2 ^ t := by grind

open Lean Grind

example (x y : Nat) : x + y = 1 → y + x = 1 := by
  grind -lia -linarith

example (x y : Nat) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind -lia -linarith

example (x y : Nat) : x + y = 1 → x + z + y = 2 → z = 0 → False := by
  grind -lia -linarith

example [CommSemiring α] [AddRightCancel α] [IsCharP α 0] (x y z : α)
    : x + y = 1 → x + z + y = 2 → z = 0 → False := by
  grind -lia -linarith

example (x y : Nat) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind

example [CommSemiring α] [AddRightCancel α] (x y : α) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind -lia -linarith

example [CommSemiring α] [AddRightCancel α] (x y : α) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind

example [CommSemiring α] [AddRightCancel α] [IsCharP α 0] (x y : α) : x^2*y = 1 → x*y^2 = y → x + y = 1 → False := by
  grind

/--
trace: [grind.ring.assert.basis] ↑x + ↑y + -2 = 0
[grind.ring.assert.basis] ↑y ^ 3 + -4 * ↑y ^ 2 + 4 * ↑y + -1 = 0
[grind.ring.assert.basis] 2 * ↑y ^ 2 + -3 * ↑y + 1 = 0
[grind.ring.assert.basis] ↑y + -1 = 0
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.ring.assert.basis true in
example [CommSemiring α] [AddRightCancel α] [IsCharP α 0] (x y : α) : x^2*y = 1 → x*y^2 = y → x + y = 2 → False := by
  grind

example [CommSemiring α] [AddRightCancel α] (x y : α) : x^2*y = 1 → x*y^2 = y → y*x = 1 := by
  grind

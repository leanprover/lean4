set_option grind.warning false

open Lean.Grind

example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b : α)
    : (2:Int)*a + b < b + a + a → False := by
  grind

example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b : α)
    : (2:Int)*a + b < b + a + a → False := by
  grind

example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b : α)
    : (2:Int)*a + b < b + a + a → False := by
  fail_if_success grind -linarith
  grind

example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b : α)
    : (2:Int)*a + b ≥ b + a + a := by
  grind

#guard_msgs (drop error) in
example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b : α)
    : (2:Int)*a + b ≥ b + a + a := by
  fail_if_success grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : 2*a + b < b + a + a → False := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : 2 + 2*a + b + 1 < b + a + a + 3 → False := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b : α)
    : 2 + 2*a + b + 1 <= b + a + a + 3 := by
  grind

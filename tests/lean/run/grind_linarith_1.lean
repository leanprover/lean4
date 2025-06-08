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

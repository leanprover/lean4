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

example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b c : α)
    : a < b → b < c → c < a → False := by
  grind

example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b c : α)
    : a < b → b < c → a < c := by
  grind

example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b c : α)
    : a < b → b ≤ c → a < c := by
  grind

example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b c : α)
    : a ≤ b → b ≤ c → a ≤ c := by
  grind

example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b c d : α)
    : a < b → b < c + d → a - d < c := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c d : α)
    : a < b → b < c + d → a - d < c := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b c : α)
    : a < b → 2*b < c → c < 2*a → False := by
  grind

-- Test misconfigured instances
/--
trace: [grind.issues] type is an ordered `IntModule` and a `Ring`, but is not an ordered ring, failed to synthesize
      Ring.IsOrdered α
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.issues true in
example [CommRing α] [Preorder α] [IntModule.IsOrdered α] (a b c : α)
    : a < b → b + b < c → c < a → False := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : a < 2 → b < a → b > 5 → False := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : a < One.one + 4 → b < a → b ≥ 5 → False := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : a < One.one + 5 → b < a → b ≥ 5 → False := by
  fail_if_success grind
  sorry

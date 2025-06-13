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

example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b c d : α)
    : a < c → b = a + d → b - d > c → False := by
  grind

example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b c d : α)
    : a + d < c → b = a + (2:Int)*d → b - d > c → False := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : a < 2 → b = a → b > 5 → False := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : a < 2 → a = b + b → b > 5 → False := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b : α)
    : a < 2 → a = b + b → b < 1 := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b : α)
    : a ≤ 2 → a + b = 3*b → b ≤ 1 := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c d e : α) :
    2*a + b ≥ 1 → b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0
    → a ≥ 3*c → c ≥ 6*e → d - e*5 ≥ 0
    → a + b + 3*c + d + 2*e ≥ 0 := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b c d e : α) :
    2*a + b ≥ 1 → b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0
    → a ≥ 3*c → c ≥ 6*e → d - e*5 ≥ 0
    → a + b + 3*c + d + 2*e < 0 → False := by
  grind

example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : a = 0 → b = 1 → a + b > 2 → False := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c : α)
    : a = 0 → a + b > 2 → b = c → 1 = c → False := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b : α)
    : a = 0 → b = 1 → a + b ≤ 2 := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b : α)
    : a*b + b*a > 1 → a*b > 0 := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c : α)
    : a*b + c > 1 → c = b*a → a*b > 0 := by
  grind

-- It must not internalize subterms `b + c + d` and `b + b + d`
#guard_msgs (trace) in
set_option trace.grind.linarith.internalize true
example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c d : α)
    : a < b + c + d → c = b → a < b + b + d := by
  grind

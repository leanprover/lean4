/-!
Model-based theory combination treats products, quotients and remainders by a numeral as
interpreted by `lia`, for `Nat` as well as `Int` numerals. It must not case-split on `x = y`
below, only on the arguments of the uninterpreted `f`.
-/

set_option trace.grind.mbtc true

/--
trace: [grind.mbtc] 3 * x = 3 * y
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x y : Nat) (f : Nat → Nat) (h₁ : f (x * 3) = 1) (h₂ : f (y * 3) = 2) (h : x ≤ y) : False := by
  fail_if_success grind
  sorry

/--
trace: [grind.mbtc] x / 3 = y / 3
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x y : Nat) (f : Nat → Nat) (h₁ : f (x / 3) = 1) (h₂ : f (y / 3) = 2) (h : x ≤ y) : False := by
  fail_if_success grind
  sorry

/--
trace: [grind.mbtc] x % 3 = y % 3
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example (x y : Nat) (f : Nat → Nat) (h₁ : f (x % 3) = 1) (h₂ : f (y % 3) = 2) (h : x ≤ y) : False := by
  fail_if_success grind
  sorry

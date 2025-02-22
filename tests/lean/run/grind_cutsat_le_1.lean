set_option grind.warning false

/--
info: [grind.cutsat.assign] a := 3
[grind.cutsat.assign] b := -1
-/
#guard_msgs (info) in
set_option trace.grind.cutsat.assign true in
example (a b : Int) (h₁ : a ≤ 3) (h₂ : a > 2) (h₃ : a + b < 3) : False := by
  fail_if_success grind
  sorry

example (a : Int) (h₁ : a ≤ 3) (h₂ : a > 5) : False := by
  grind

example (a b : Int) (h₁ : a ≤ 3) (h₂ : a + b > 5) (h₃ : a - b > 1) : False := by
  grind

example (a b c : Int) (h₁ : a ≤ 3) (h₂ : a + b > 5) (h₃ : a - c > 1) : b ≤ c → c ≤ b → False := by
  grind

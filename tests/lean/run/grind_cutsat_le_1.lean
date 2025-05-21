set_option grind.warning false
set_option grind.debug true

/--
trace: [grind.debug.cutsat.search.assign] b := -1
[grind.debug.cutsat.search.assign] a := 3
-/
#guard_msgs (trace) in
set_option trace.grind.debug.cutsat.search.assign true in
example (a b : Int) (h₁ : a ≤ 3) (h₂ : a > 2) (h₃ : a + b < 3) : False := by
  fail_if_success grind
  sorry

example (a : Int) (h₁ : a ≤ 3) (h₂ : a > 5) : False := by
  grind

example (a b : Int) (h₁ : a ≤ 3) (h₂ : a + b > 5) (h₃ : a - b > 1) : False := by
  grind

example (a b c : Int) (h₁ : a ≤ 3) (h₂ : a + b > 5) (h₃ : a - c > 1) : b ≤ c → c ≤ b → False := by
  grind

theorem ex₁ (a b c : Int) (h₁ : a ≤ 3) (h₂ : a + b > 5) (h₃ : a - c > 1) : b ≤ c → c ≤ b → False := by
  grind

open Int.Linear in
#print ex₁

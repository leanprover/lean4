/-- trace: [grind.cutsat.model] a := 2 -/
#guard_msgs (trace) in
set_option trace.grind.cutsat.model true in
example (a b : Int) : a ≤ 5 → a ≠ 4 → 2 ∣ a → False := by
  (fail_if_success grind); sorry

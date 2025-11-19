module
/--
trace: [grind.lia.model] a := 2
[grind.lia.model] b := 1
-/
#guard_msgs (trace) in
set_option trace.grind.lia.model true in
example (a b : Int) : a ≤ 5 → a ≠ 4 → 2 ∣ a → False := by
  (fail_if_success grind); sorry

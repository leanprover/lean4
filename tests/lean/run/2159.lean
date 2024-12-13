/--
info: ⊢ 1.2 < 2
---
info: ⊢ 1.2 < 2
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 1.2 < 2 := by
  trace_state
  fail_if_success simp only
  trace_state
  sorry

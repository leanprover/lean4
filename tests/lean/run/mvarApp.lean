/-!
# Allowing metavariable applications in elaborator
-/


/--
info: f : Nat → Nat → Prop := Eq
⊢ 2 = 3
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : 2 = 3 := by
  change ?f 2 3
  let f := ?f
  trace_state
  sorry

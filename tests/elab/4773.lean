/--
error: Tactic `exact` failed: attempting to close the goal using
  ?loop
this is often due to an occurs-check failure

case loop
⊢ False
-/
#guard_msgs in
example : False := by
  refine ?loop
  exact ?loop

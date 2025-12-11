set_option pp.mvars false

/--
error: Failed to infer type of theorem `foo`

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be
---
error: type of theorem `foo` is not a proposition
  ?_
-/
#guard_msgs (error) in
theorem foo : _ :=
  sorry

/--
error: Failed to infer type of example

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
-/
#guard_msgs (error) in
example : _ :=
  sorry

/--
error: Failed to infer type of definition `boo`

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
-/
#guard_msgs (error) in
def boo : _ :=
  sorry

/--
error: Failed to infer type of instance `boo`

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
-/
#guard_msgs (error) in
instance boo : _ :=
  sorry

/--
error: Failed to infer type of instance

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
-/
#guard_msgs (error) in
instance : _ :=
  sorry

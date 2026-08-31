/-! Check messages of binder type inference failures. -/

/--
error: Failed to infer type of binder `y`
---
error: Failed to infer type of binder `x`
---
error: Failed to infer type of definition `l1`
-/
#guard_msgs in
def l1 := fun x y => x

/--
error: Failed to infer binder type
---
error: Failed to infer type of definition `l2`
-/
#guard_msgs in
def l2 := fun _ => 0

/--
error: Failed to infer type of theorem `t`

Note: All parameter types and holes (e.g., `_`) in the header of a theorem are resolved before the proof is processed; information from the proof cannot be used to infer what these values should be
---
error: type of theorem `t` is not a proposition
  ?m.1
-/
#guard_msgs in
theorem t : _ := _

/--
error: Failed to infer type of example

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
-/
#guard_msgs in
example : _ := _

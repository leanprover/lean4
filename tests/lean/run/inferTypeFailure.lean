/-! Check messages of binder type inference failures. -/

/--
error: Failed to infer type of binder 'y'
---
error: Failed to infer type of binder 'x'
---
error: Failed to infer type of definition 'l1'
-/
#guard_msgs in
def l1 := fun x y => x

/--
error: Failed to infer binder type
---
error: Failed to infer type of definition 'l2'
-/
#guard_msgs in
def l2 := fun _ => 0

/--
error: Failed to infer type of theorem 't'
when the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
---
error: type of theorem 't' is not a proposition
  ?m.65
-/
#guard_msgs in
theorem t : _ := _

/--
error: Failed to infer type of example
when the resulting type of a declaration is explicitly provided, all holes (e.g., `_`) in the header are resolved before the declaration body is processed
-/
#guard_msgs in
example : _ := _

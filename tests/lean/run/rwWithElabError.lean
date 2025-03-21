/-!
# Test for error reporting when `rw`/`rewrite` has an elaboration error
-/

/-!
Elaboration failures abort tactic evaluation.
Before, the second error was
```
error: tactic 'rewrite' failed, equality or iff proof expected
  ?m.5
⊢ True
```
-/
/--
error: unknown identifier 'not_a_theorem'
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  rewrite [not_a_theorem]

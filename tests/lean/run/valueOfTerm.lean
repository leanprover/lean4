/-!
# Testing the `value_of%` term elaborator
-/

/-!
Basic case of success for local definitions.
-/
/--
trace: x : Nat := 1 + 1
hx : x = 1 + 1
⊢ True
-/
#guard_msgs in
example : True := by
  let x := 1 + 1
  have hx : x = value_of% x := rfl
  trace_state
  trivial

/-!
Basic case of success for global constants.
Note that it evaluates to a lambda with an implicit parameter.
-/
/--
trace: hx : @id = fun {α} a => a
⊢ True
-/
#guard_msgs in
example : True := by
  have hx : @id.{1} = value_of% id := rfl
  trace_state
  trivial


/-!
Referring to a global constant with no value.
-/
/--
error: Constant has no value.
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  let a := value_of% True

/-!
Referring to a non-existent identifier, error.
-/
/--
error: Unknown constant `_TESTS_LEAN_RUN_VALUETERM_not_used_in_Lean`
---
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by
  let a := value_of% _TESTS_LEAN_RUN_VALUETERM_not_used_in_Lean

/-!
Referring to a cdecl, error since no value.
-/
/-- error: Local declaration has no value. -/
#guard_msgs in
example : True := by
  have x := 1 + 1
  have hx : x = value_of% x := rfl

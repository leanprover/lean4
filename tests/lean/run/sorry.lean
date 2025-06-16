/-!
# Tests of the `sorry` term elaborator
-/

set_option pp.mvars false

/-!
Basic usage.
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : False := sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in example : False := by sorry

/-!
Pretty printing
-/

/-- info: sorry : Nat -/
#guard_msgs in #check (sorry : Nat)

/-- info: fun x => sorry : Nat → Nat -/
#guard_msgs in #check fun x : Nat => (sorry : Nat)

/-- info: fun x => sorry (x + 1) : Nat → Nat -/
#guard_msgs in #check fun x : Nat => (sorry : Nat → Nat) (x + 1)

/-!
Uniqueness
-/

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : (sorry : Nat) = sorry := by
  fail_if_success rfl
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
def f (n : Nat) : Nat → Nat := sorry

example : f 0 0 = f 0 0 := rfl -- succeeds

/-!
If `sorry` is used for a function type, then one gets a family of unique `sorry`s.
-/
/--
error: type mismatch
  rfl
has type
  ?_ = ?_ : Prop
but is expected to have type
  f 0 1 = f 0 0 : Prop
-/
#guard_msgs in example : f 0 1 = f 0 0 := rfl

/-!
It is not completely unique though. The `sorry` did not pay attention to variables in the local context.
-/
#guard_msgs in example : f 1 0 = f 0 0 := rfl

/-!
Showing source position when surfacing differences.
-/
-- note: the module name is `sorry` and not `lean.run.sorry` in the testing environment,
-- so this test fails in VS Code.
/--
error: type mismatch
  sorry
has type
  sorry `«sorry:77:43» : Sort _
but is expected to have type
  sorry `«sorry:77:25» : Sort _
-/
#guard_msgs in example : sorry := (sorry : sorry)

/-!
Elaboration errors are just labeled, not unique, to limit cascading errors.
-/
/--
error: unknown identifier 'a'
---
error: unknown identifier 'b'
---
info: ⊢ sorry = sorry
-/
#guard_msgs in
set_option autoImplicit false in
example : a = b := by trace_state; rfl

/-!
Showing that the sorries in the previous test are labeled.
-/
/--
error: unknown identifier 'a'
---
error: unknown identifier 'b'
---
info: ⊢ sorry `«sorry:106:10» = sorry `«sorry:106:14»
-/
#guard_msgs in
set_option autoImplicit false in
set_option pp.sorrySource true in
example : a = b := by trace_state; rfl

/-!
The local context should show `sorry` without showing its source position.
This requires `Lean.Widget.ppExprTagged` to have a pretty printing mode that doesn't override any pretty printing options.
https://github.com/leanprover/lean4/issues/6715
-/
/--
info: n : Nat := sorry
⊢ True
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example : True := by
  let n : Nat := sorry
  trace_state
  trivial

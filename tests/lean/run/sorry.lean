/-!
# Tests of the `sorry` term elaborator
-/

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
  f 0 1 = f 0 1 : Prop
but is expected to have type
  f 0 1 = f 0 0 : Prop
-/
#guard_msgs in example : f 0 1 = f 0 0 := rfl

/-!
It is not completely unique though. The `sorry` did not pay attention to variables in the local context.
-/
#guard_msgs in example : f 1 0 = f 0 0 := rfl

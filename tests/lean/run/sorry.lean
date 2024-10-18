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

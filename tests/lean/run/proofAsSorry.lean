set_option debug.proofAsSorry true
set_option pp.mvars false

/--
error: type mismatch
  rfl
has type
  ?_ = ?_ : Prop
but is expected to have type
  2 + 2 = 5 : Prop
-/
#guard_msgs in
example : 2 + 2 = 5 := rfl -- This is not a theorem

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem ex : 2 + 2 = 5 := rfl

#guard_msgs in
def data (w : Nat) : String := toString w

/-- info: "37" -/
#guard_msgs in
#eval data 37

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem tst1 : 0 + x = 1*x + 0 := by
  simp

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem tst2 : ∀ x, 0 + x = 1*x + 0 := by
  intro x
  simp

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem tst3 : x = 2*x + 1 := by
  rfl

#guard_msgs in
def concatSelf (as : List α) := as ++ as

/-- info: [1, 2, 3, 1, 2, 3] -/
#guard_msgs in
#eval concatSelf [1, 2, 3]

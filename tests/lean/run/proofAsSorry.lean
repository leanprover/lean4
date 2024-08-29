set_option debug.proofAsSorry true

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : 2 + 2 = 5 := rfl

#guard_msgs in
def data (w : Nat) : String := toString w

/-- info: "37" -/
#guard_msgs in
#eval data 37

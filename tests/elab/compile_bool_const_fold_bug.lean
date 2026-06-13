/-! This is a regression test for a bug in the LCNF simp constant folder for Bool -/

@[noinline]
def myBool := true

def a := (Bool.decEq myBool true).decide

/-- info: true -/
#guard_msgs in
#eval a

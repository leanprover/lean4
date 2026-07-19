/-!
Regression test that the rename of `Parser.Term.liftMethod` to `Parser.Term.nestedAction`
did not change the syntax or semantics accepted by the legacy `do` elaborator.
-/

set_option backward.do.legacy true

def tst (x : Nat) : IO Bool := do
  if (← pure x) == 0 then
    return true
  pure (x == 1)

/-- info: true -/
#guard_msgs in
#eval tst 0

/-- info: true -/
#guard_msgs in
#eval tst 1

/-- info: false -/
#guard_msgs in
#eval tst 2

def tstReturn (x : Nat) : IO Nat := do
  return (← pure 42) + x

/-- info: 47 -/
#guard_msgs in
#eval tstReturn 5

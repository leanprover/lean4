
def tst (x : Nat) : IO Unit := do
if x == 0 then
  IO.println "x is zero"
else
  if x == 1 then
    IO.println "x is one"
  throw $ IO.userError "x is not zero"

/-- info: x is zero -/
#guard_msgs in
#eval tst 0


def f (x : Nat) : IO Unit := do
if x > 10 then
  return
throw $ IO.userError "x ≤ 10"

#guard_msgs in
#eval f 11

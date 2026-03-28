-- works
#guard_msgs in
def go (numDigits : Nat) : Nat :=
  if 4*numDigits < 64 then
    go (numDigits+1)
  else
    numDigits
termination_by 64 - 4*numDigits

-- set_option trace.Elab.definition.wf true
-- set_option debug.rawDecreasingByGoal true

#guard_msgs(pass trace, all) in
def foo (numDigits : Nat) : Nat :=
  let sz := 4*numDigits
  if sz < 64 then
    foo (numDigits+1)
  else
    numDigits
termination_by 64 - 4*numDigits

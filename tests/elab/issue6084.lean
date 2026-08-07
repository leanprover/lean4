import Lean

open Lean Meta

def Foo := True

def Bar := Foo → Foo

/-- info: True → True -/
#guard_msgs in
run_meta do
  logInfo (← reduceAll (.const ``Bar []))

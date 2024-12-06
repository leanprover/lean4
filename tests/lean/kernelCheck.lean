import Lean

/-!
The kernel should catch misbehaving tactics.
NOTE that this test should **NOT** use `#guard_msgs` as it disables parallelism, which is the main
thing we want to test here.
-/

open Lean Elab Tactic

elab "wrong" : tactic => do
  let mvar ← getMainGoal
  mvar.assign <| .const ``True []

theorem no : False := by wrong

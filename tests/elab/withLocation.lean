import Lean

open Lean Elab Tactic
elab "test" : tactic => do
  withLocation (.targets #[] true) (fun _ => return ())
    do
      let some (_, lhs, _) := (← getMainTarget).eq? | failure
      logInfo <| ← FVarId.getUserName (lhs.fvarId!)
    (fun _ => return ())

example : 1 = 1 := by
  let t := 1
  show t = 1
  test
  sorry

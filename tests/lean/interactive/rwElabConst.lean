import Lean
open Lean PrettyPrinter Delaborator SubExpr
@[delab app.Eq]
def checkUniv : Delab := do
  let .const _ [.mvar u] := (← getExpr).getAppFn | failure
  _ ← u.getLevel
  failure

example : True := by
  try rw [eq_self]
          --^ $/lean/plainTermGoal
  trivial

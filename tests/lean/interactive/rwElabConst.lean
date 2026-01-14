import Lean

/-!
Previously, `rw [my_lemma]` would elaborate `my_lemma` twice, both times generating new universe metavariables.
This caused the "Expected type" to contain a universe metavariable that wasn't in the metavariable context.

This test verifies that the generated universe level is in the metavariable context.
-/

open Lean PrettyPrinter Delaborator SubExpr
/-- No-op delaborator that checks that the universe level is in the metavariable context -/
@[delab app.Eq]
def checkUniv : Delab := do
  let .const _ [.mvar u] := (← getExpr).getAppFn | failure
  _ ← u.getLevel -- if `u` isn't in the metavariable context, this throws an error during elaboration
  failure

example : True := by
  try rw [eq_self]
          --^ $/lean/plainTermGoal
  trivial

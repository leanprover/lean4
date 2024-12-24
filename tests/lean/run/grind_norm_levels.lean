import Lean

def g {α : Sort u} (a : α) := a

open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    let nodes ← filterENodes fun e => return e.self.isAppOf ``g
    logInfo (nodes.toList.map (·.self))

-- `grind` final state must contain only two `g`-applications
/--
info: [g (a, b), g (g (a, b))]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example {β : Type v} {α : Type u} (a c : α) (b d : β) : g.{max u v + 1} (a, b) = (c, d) → g (g.{max (u+1) (v+1)} (a, b)) = (c, d) → False := by
  grind_test
  sorry

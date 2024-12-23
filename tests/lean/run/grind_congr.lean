import Lean

def f (a : Nat) := a + a + a

-- Prints the equivalence class containing a `f` application
open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    let #[n, _] ← filterENodes fun e => return e.self.isAppOf ``f | unreachable!
    let eqc ← getEqc n.self
    logInfo eqc

/--
info: [d, f b, c, f a]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b c d : Nat) : a = b → f a = c → f b = d → False := by
  grind_test
  sorry

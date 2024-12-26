import Lean

def f (a : Nat) := a + a + a
def g (a : Nat) := a + a

-- Prints the equivalence class containing a `f` application
open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    let #[n, _] ← filterENodes fun e => return e.self.isAppOf ``f | unreachable!
    let eqc ← getEqc n.self
    logInfo eqc

set_option grind.debug true
set_option grind.debug.proofs true

/--
info: [d, f b, c, f a]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b c d : Nat) : a = b → f a = c → f b = d → False := by
  grind_test
  sorry

/--
info: [d, f b, c, f a]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b c d : Nat) : f a = c → f b = d → a = b → False := by
  grind_test
  sorry

/--
info: [d, f (g b), c, f (g a)]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b c d e : Nat) : f (g a) = c → f (g b) = d → a = e → b = e → False := by
  grind_test
  sorry

/--
info: [d, f (g b), c, f v]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b c d e v : Nat) : f v = c → f (g b) = d → a = e → b = e → v = g a → False := by
  grind_test
  sorry

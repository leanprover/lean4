import Lean


def g (s : Type) := s
def f (a : α) := a

open Lean Meta Elab Tactic Grind in
elab "grind_test" : tactic => withMainContext do
  let declName := (← Term.getDeclName?).getD `_main
  Meta.Grind.preprocessAndProbe (← getMainGoal) declName do
    let nodes ← filterENodes fun e => return e.self.isAppOf ``f
    logInfo (nodes.toList.map (·.self))


set_option pp.explicit true
/--
info: [@f Nat a, @f Nat b]
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
example (a b c d : Nat) : @f Nat a = b → @f (g Nat) a = c → @f (g Nat) b = d → a = b → False := by
  -- State should have only two `f`-applications: `@f Nat a`, `@f Nat b`
  -- Note that `@f (g Nat) b` has been canonicalized to `@f Nat b`.
  -- Thus, if `a` and `b` equivalence classes are merged, `grind` can still detect that
  -- `@f Nat a` and `@f Nat b` are equal too.
  grind_test
  sorry

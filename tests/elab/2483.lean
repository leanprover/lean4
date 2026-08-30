import Lean

/-!
# Make sure `Lean.exprDependsOn'` takes delayed assignments into account
https://github.com/leanprover/lean4/issues/2483

This file is a slightly minimized version of the test case by Kim Morrison.
-/

open Lean Meta Elab Term Tactic

set_option pp.mvars.anonymous false

/--
Check if a goal is "independent" of a list of other goals.
We say a goal is independent of other goals if assigning a value to it
can not change the solvability of the other goals.

This function only calculates a conservative approximation of this condition.
-/
def Lean.MVarId.independent? (L : List MVarId) (g : MVarId) : MetaM Bool := do
  let t ← instantiateMVars (← g.getType)
  if t.hasExprMVar then
    -- If the goal's type contains other meta-variables,
    -- we conservatively say that `g` is not independent.
    return false
  -- Finally, we check if the goal `g` appears in the type of any of the goals `L`.
  let r ← L.allM fun g' => do
    let t' ← pure (← g'.getType)
    pure <| !(← exprDependsOn' t' (.mvar g))
  return r

elab "test_indep" : tactic => do
  let gs ← getGoals
  for g in gs do
    guard !(← g.independent? gs) <|> throwError m!"{g} was incorrectly considered independent!"

/-!
This test worked before.
Correctly, `independent?` claims neither goal is independent:
`?snd` because its type contains a metavariable,
and `?fst` because `?snd`'s type depends on it
-/
/--
trace: case snd
⊢ Option ?fst

case fst
⊢ Type _
-/
#guard_msgs in
example : Σ α, Option α := by
  constructor
  trace_state
  test_indep
  exact some 0

/-!
This test failed before.
Introducing a hypothesis in the `fst` goal introduces a delayed assignment.
This previously used to cause `independent?` to incorrectly think `?fst` is independent,
but now it's not independent.
-/
/--
trace: case fst
this : Nat
⊢ Type _

case snd
⊢ Option
    (have this := 0;
    ?_ this)
---
trace: case fst
this : Nat
⊢ Type _

case snd
⊢ Option
    (have this := 0;
    ?fst)
-/
#guard_msgs in
example : Σ α, Option α := by
  constructor
  case' fst => have := 0
  -- `?_ this` in output demonstrates existence of delayed assignment:
  set_option pp.mvars.delayed true in trace_state
  trace_state
  test_indep
  case snd => exact some 0

import Lean

/-! Ensures that `refine` does not remove pre-existing natural goals from the goal list. -/

open Lean Meta Elab Tactic Term

elab "add_natural_goal" s:ident " : " t:term : tactic => do
  let g ← mkFreshExprMVar (← elabType t) .natural s.getId
  appendGoals [g.mvarId!]

/-!

In the following, `refine` would erroneously close each focused goal, leading to a
`(kernel) declaration has metavariables '_example'` error.

This occurred because `withCollectingNewGoalsFrom` was only erroring on new natural goals (as
determined by `index`), while simultaneously only passing through non-natural goals to construct
the resulting goal list. This orphaned old natural metavariables and closed the goal list
erroneously.

As such, all of the following tests should lead to an `unsolved goals` error, followed by a
`no goals` error (instead of a successful focus).

-/

example : Bool × Nat := by
  add_natural_goal d : Bool
  add_natural_goal e : Nat
  · refine (?d,?e)
  · refine ?d
  · refine ?e

example : Bool × Bool := by
  add_natural_goal d : Bool
  add_natural_goal e : Bool
  · refine (?d,?e)
  · case d => refine ?e
  · refine ?e

/-!

Previously, this would error, as `refine (?d, ?e)` erroneously closed the goal, leading to a
`no goals` error. Instead, this should succeed.

-/

example : Bool × Bool := by
  add_natural_goal d : Bool
  add_natural_goal e : Bool
  · refine (?d,?e)
    refine ?d
    refine ?e   -- This unifies `?d` and `?e`, so only one goal remains.
    exact true

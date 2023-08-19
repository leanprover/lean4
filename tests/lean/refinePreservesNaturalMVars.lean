import Lean

open Lean Meta Elab Tactic Term

elab "add_natural_goal" s:ident " : " t:term : tactic => do
  let g ← mkFreshExprMVar (← elabType t) .natural s.getId
  appendGoals [g.mvarId!]

elab "add_synthetic_goal" s:ident " : " t:term : tactic => do
  let g ← mkFreshExprMVar (← elabType t) .syntheticOpaque s.getId
  appendGoals [g.mvarId!]

-- Should not yield (kernel) declaration includes metavariables;
-- instead, should error

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

-- Should not error:

example : Bool × Bool := by
  add_natural_goal d : Bool
  add_natural_goal e : Bool
  · refine (?d,?e)
    refine ?d
    refine ?e
    exact true

/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind

/-!
Combinators for manipulating `GrindTactic`s.
TODO: a proper tactic language for `grind`.
-/

def GrindTactic := Goal → GrindM (Option (List Goal))

partial def GrindTactic.iterate (x : GrindTactic) : GrindTactic := fun goal => do
  go [goal] []
where
  go (todo : List Goal) (result : List Goal) : GrindM (List Goal) := do
    match todo with
    | [] => return result
    | goal :: todo =>
      if let some goalsNew ← x goal then
        go (goalsNew ++ todo) result
      else
        go todo (goal :: result)

def toGrindTactic (f : GoalM Unit) : GrindTactic := fun goal => do
  let goal ← GoalM.run' goal f
  if goal.inconsistent then
    return some []
  else
    return some [goal]

def GrindTactic' := Goal → GrindM (List Goal)

def GrindTactic'.toGrindTactic (x : GrindTactic') : GrindTactic := fun goal => do
  let goals ← x goal
  return some goals

end Lean.Meta.Grind

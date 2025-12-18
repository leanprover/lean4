/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Finish
public section
namespace Lean.Meta.Grind
/--
Try to solve/close the given goal.
Returns `some goal` if this subgoal failed to be closed,
and `none` if all subgoals were closed.
-/
def solve (goal : Goal) : GrindM (Option Goal) := do
  let a ← Action.mkFinish
  match (← a.run goal) with
  | .closed _ => return none
  | .stuck gs =>
    let goal :: _ := gs | return some goal
    return goal

end Lean.Meta.Grind

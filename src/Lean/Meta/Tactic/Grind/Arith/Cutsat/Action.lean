/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
public import Lean.Meta.Tactic.Grind.Action
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
namespace Lean.Meta.Grind.Action

/-- Linear integer arithmetic action. -/
public def lia : Action := fun goal kna kp => do
  let (progress, goal') ← GoalM.run goal Meta.Grind.Arith.Cutsat.check
  if progress then
    let r ← kp goal'
    /-
    **Note**: `Cutsat.check` may make progress by computing a valid assignment satisfying all constraints.
    That said, unless it closed the goal, it is pointless to include a `lia` tactic in the resulting tactic
    sequence because no information has been communicated to the other solvers.
    -/
    if goal'.inconsistent then
      concatTactic r `(grind| lia)
    else
      return r
  else
    kna goal'

end Lean.Meta.Grind.Action

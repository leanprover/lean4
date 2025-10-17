/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Action
import Lean.Meta.Tactic.Grind.AC.Eq
namespace Lean.Meta.Grind.Action

/-- Linear integer arithmetic action. -/
public def ac : Action := fun goal kna kp => do
  let (result, goal') ← GoalM.run goal AC.check
  match result with
  | .none       => kna goal'
  | .progress   => kp goal'
  | .propagated => concatTactic (← kp goal') `(grind| ac)
  | .closed     => closeWith `(grind| ac)

end Lean.Meta.Grind.Action

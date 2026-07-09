/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Tactic.Cbv.Main
namespace Lean.Elab.Tactic.Grind
open Meta Grind

@[builtin_grind_tactic Parser.Tactic.Grind.symCbv] def evalSymCbv : GrindTactic := fun _ => withMainContext do
  ensureSym
  let goal ← getMainGoal
  let result ← liftGrindM <|
    Lean.Meta.Tactic.Cbv.cbvGoalCore goal.mvarId
  match result with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [{ goal with mvarId }]

end Lean.Elab.Tactic.Grind

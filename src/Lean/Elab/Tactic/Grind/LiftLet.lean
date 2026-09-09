/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Sym.LiftLet
import Lean.Meta.Tactic.Replace
namespace Lean.Elab.Tactic.Grind
open Meta

@[builtin_grind_tactic Parser.Tactic.Grind.symLiftLets] def evalSymLiftLets : GrindTactic := fun _ => withMainContext do
  ensureSym
  let goal ← getMainGoal
  let target ← goal.mvarId.getType
  let target' ← liftSymM <| Sym.liftLets target
  if Sym.isSameExpr target target' then
    throwError "`lift_lets` made no progress"
  let mvarId ← goal.mvarId.replaceTargetDefEq target'
  replaceMainGoal [{ goal with mvarId }]

end Lean.Elab.Tactic.Grind

/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Grind.RevertAll
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Proj
import Lean.Meta.Tactic.Grind.ForallProp
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Inv
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.EMatch

namespace Lean.Meta.Grind

def mkMethods : CoreM Methods := do
  let builtinPropagators ← builtinPropagatorsRef.get
  return {
    propagateUp := fun e => do
     propagateForallProp e
     let .const declName _ := e.getAppFn | return ()
     propagateProjEq e
     if let some prop := builtinPropagators.up[declName]? then
       prop e
    propagateDown := fun e => do
     let .const declName _ := e.getAppFn | return ()
     if let some prop := builtinPropagators.down[declName]? then
       prop e
  }

def GrindM.run (x : GrindM α) (mainDeclName : Name) (config : Grind.Config) : MetaM α := do
  let scState := ShareCommon.State.mk _
  let (falseExpr, scState) := ShareCommon.State.shareCommon scState (mkConst ``False)
  let (trueExpr, scState)  := ShareCommon.State.shareCommon scState (mkConst ``True)
  let thms ← grindNormExt.getTheorems
  let simprocs := #[(← grindNormSimprocExt.getSimprocs)]
  let simp ← Simp.mkContext
    (config := { arith := true })
    (simpTheorems := #[thms])
    (congrTheorems := (← getSimpCongrTheorems))
  x (← mkMethods).toMethodsRef { mainDeclName, config, simprocs, simp } |>.run' { scState, trueExpr, falseExpr }

private def mkGoal (mvarId : MVarId) : GrindM Goal := do
  let trueExpr ← getTrueExpr
  let falseExpr ← getFalseExpr
  let thmMap ← getEMatchTheorems
  GoalM.run' { mvarId, thmMap } do
    mkENodeCore falseExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore trueExpr (interpreted := true) (ctor := false) (generation := 0)

private def initCore (mvarId : MVarId) : GrindM (List Goal) := do
  mvarId.ensureProp
  -- TODO: abstract metavars
  mvarId.ensureNoMVar
  let mvarId ← mvarId.clearAuxDecls
  let mvarId ← mvarId.revertAll
  let mvarId ← mvarId.unfoldReducible
  let mvarId ← mvarId.betaReduce
  let goals ← intros (← mkGoal mvarId) (generation := 0)
  goals.forM (·.checkInvariants (expensive := true))
  return goals.filter fun goal => !goal.inconsistent

def all (goals : List Goal) (f : Goal → GrindM (List Goal)) : GrindM (List Goal) := do
  goals.foldlM (init := []) fun acc goal => return acc ++ (← f goal)

/-- A very simple strategy -/
private def simple (goals : List Goal) : GrindM (List Goal) := do
  all goals ematchStar

def main (mvarId : MVarId) (config : Grind.Config) (mainDeclName : Name) : MetaM (List MVarId) := do
  let go : GrindM (List MVarId) := do
    let goals ← initCore mvarId
    let goals ← simple goals
    trace[grind.debug.final] "{← ppGoals goals}"
    return goals.map (·.mvarId)
  go.run mainDeclName config

/-- Helper function for debugging purposes -/
def preprocessAndProbe (mvarId : MVarId) (mainDeclName : Name) (p : GoalM Unit) : MetaM Unit :=
  let go : GrindM Unit := do
    let goals ← initCore mvarId
    trace[grind.debug.final] "{← ppGoals goals}"
    goals.forM fun goal =>
      discard <| GoalM.run' goal p
    return ()
  withoutModifyingMCtx do
    go.run mainDeclName {}

end Lean.Meta.Grind

/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Canonicalizer
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RevertAll
import Lean.Meta.Tactic.Grind.EnsureNoMVar
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Util

namespace Lean.Meta.Grind
namespace Preprocessor

-- TODO: use congruence closure and decision procedures during pre-processing
-- TODO: implement `simp` discharger using preprocessor state

structure Context where
  simp     : Simp.Context
  simprocs : Array Simp.Simprocs
  deriving Inhabited

structure State where
  todo  : List Goal := []
  simpStats : Simp.Stats := {}
  deriving Inhabited

abbrev PreM := ReaderT Context $ StateRefT State GrindM

def mkInitialState (mvarId : MVarId) : State :=
  { todo := [ mkGoal mvarId ] }

def PreM.run (x : PreM α) (mvarId : MVarId) : GrindM α := do
  let thms ← grindNormExt.getTheorems
  let simprocs := #[(← grindNormSimprocExt.getSimprocs)]
  let simp : Simp.Context := {
    config := { arith := true }
    simpTheorems := #[thms]
    congrTheorems := (← getSimpCongrTheorems)
  }
  x { simp, simprocs } |>.run' (mkInitialState mvarId)

def simpHyp? (mvarId : MVarId) (fvarId : FVarId) : PreM (Option (FVarId × MVarId)) := do
  let simpStats := (← get).simpStats
  let (result, simpStats) ← simpLocalDecl mvarId fvarId (← read).simp (← read).simprocs (stats := simpStats)
  modify fun s => { s with simpStats }
  return result

def getNextGoal? : PreM (Option Goal) := do
  match (← get).todo with
  | [] => return none
  | goal :: todo =>
    modify fun s => { s with todo }
    return some goal

inductive IntroResult where
  | done | closed
  | newHyp (fvarId : FVarId) (goal : Goal)
  | newLocal (fvarId : FVarId) (goal : Goal)

def introNext (goal : Goal) : PreM IntroResult := do
  let target ← goal.mvarId.getType
  if target.isArrow then
    let (fvarId, mvarId) ← goal.mvarId.intro1P
    -- TODO: canonicalize subterms
    mvarId.withContext do
    if (← isProp (← fvarId.getType)) then
      let some (fvarId, mvarId) ← simpHyp? mvarId fvarId | return .closed
      return .newHyp fvarId { goal with mvarId }
    else
      return .newLocal fvarId { goal with mvarId }
  else if target.isLet || target.isForall then
    -- TODO: canonicalize subterms
    -- TODO: If forall is of the form `∀ h : <proposition>, A h`, generalize `h`.
    let (fvarId, mvarId) ← goal.mvarId.intro1P
    return .newLocal fvarId { goal with mvarId }
  else
    return .done

def pushTodo (goal : Goal) : PreM Unit :=
  modify fun s => { s with todo := goal :: s.todo }

def pushResult (goal : Goal) : PreM Unit :=
  modifyThe Grind.State fun s => { s with goals := s.goals.push goal }

end Preprocessor

open Preprocessor

partial def main (mvarId : MVarId) (mainDeclName : Name) : MetaM Grind.State := do
  mvarId.ensureNoMVar
  let mvarId ← mvarId.revertAll
  mvarId.ensureNoMVar
  let mvarId ← mvarId.abstractNestedProofs mainDeclName
  let mvarId ← mvarId.unfoldReducible
  let mvarId ← mvarId.betaReduce
  let s ← (loop *> getThe Grind.State) |>.run mvarId |>.run mainDeclName
  return s
where
  loop : PreM Unit := do
    let some goal ← getNextGoal? | return ()
    trace[Meta.debug] "{goal.mvarId}"
    match (← introNext goal) with
    | .closed => loop
    | .done =>
      -- TODO: apply `byContradiction`
      pushResult goal
      return ()
    | .newHyp fvarId goal =>
      -- TODO: apply eliminators
      let clause ← goal.mvarId.withContext do mkInputClause fvarId
      pushTodo { goal with clauses := goal.clauses.push clause }
      loop
    | .newLocal _ goal =>
      -- TODO: apply eliminators
      pushTodo goal
      loop

end Lean.Meta.Grind

/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Canonicalizer
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RevertAll
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
  simpStats : Simp.Stats := {}
  deriving Inhabited

abbrev PreM := ReaderT Context $ StateRefT State GrindM

def PreM.run (x : PreM α) : GrindM α := do
  let thms ← grindNormExt.getTheorems
  let simprocs := #[(← grindNormSimprocExt.getSimprocs)]
  let simp : Simp.Context := {
    config := { arith := true }
    simpTheorems := #[thms]
    congrTheorems := (← getSimpCongrTheorems)
  }
  x { simp, simprocs } |>.run' {}

def simp (e : Expr) : PreM Simp.Result := do
  let simpStats := (← get).simpStats
  let (r, simpStats) ← Meta.simp e (← read).simp (← read).simprocs (stats := simpStats)
  modify fun s => { s with simpStats }
  return r

def simpHyp? (mvarId : MVarId) (fvarId : FVarId) : PreM (Option (FVarId × MVarId)) := do
  let simpStats := (← get).simpStats
  let (result, simpStats) ← simpLocalDecl mvarId fvarId (← read).simp (← read).simprocs (stats := simpStats)
  modify fun s => { s with simpStats }
  return result

inductive IntroResult where
  | done
  | newHyp (fvarId : FVarId) (goal : Goal)
  | newLocal (fvarId : FVarId) (goal : Goal)

def introNext (goal : Goal) : PreM IntroResult := do
  let target ← goal.mvarId.getType
  if target.isArrow then
    goal.mvarId.withContext do
      let p := target.bindingDomain!
      if !(← isProp p) then
        let (fvarId, mvarId) ← goal.mvarId.intro1P
        return .newLocal fvarId { goal with mvarId }
      else
        let tag ← goal.mvarId.getTag
        let q := target.bindingBody!
        let r ← simp p
        let p' := r.expr
        let p' ← canon p'
        let p' ← shareCommon p'
        let fvarId ← mkFreshFVarId
        let lctx := (← getLCtx).mkLocalDecl fvarId target.bindingName! p' target.bindingInfo!
        let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances) q .syntheticOpaque tag
        let mvarIdNew := mvarNew.mvarId!
        mvarIdNew.withContext do
          let h ← mkLambdaFVars #[mkFVar fvarId] mvarNew
          match r.proof? with
          | some he =>
            let hNew := mkAppN (mkConst ``Lean.Grind.intro_with_eq) #[p, p', q, he, h]
            goal.mvarId.assign hNew
            return .newHyp fvarId { goal with mvarId := mvarIdNew }
          | none =>
            -- `p` and `p'` are definitionally equal
            goal.mvarId.assign h
            return .newHyp fvarId { goal with mvarId := mvarIdNew }
  else if target.isLet || target.isForall then
    let (fvarId, mvarId) ← goal.mvarId.intro1P
    mvarId.withContext do
      let localDecl ← fvarId.getDecl
      if (← isProp localDecl.type) then
        -- Add a non-dependent copy
        let mvarId ← mvarId.assert localDecl.userName localDecl.type (mkFVar fvarId)
        return .newLocal fvarId { goal with mvarId }
      else
        return .newLocal fvarId { goal with mvarId }
  else
    return .done

def pushResult (goal : Goal) : PreM Unit :=
  modifyThe Grind.State fun s => { s with goals := s.goals.push goal }

partial def preprocess (goal : Goal) : PreM Unit := do
  trace[Meta.debug] "{goal.mvarId}"
  match (← introNext goal) with
  | .done =>
    if let some mvarId ← goal.mvarId.byContra? then
      preprocess { goal with mvarId }
    else
      pushResult goal
  | .newHyp fvarId goal =>
    -- TODO: apply eliminators
    let clause ← goal.mvarId.withContext do mkInputClause fvarId
    preprocess { goal with clauses := goal.clauses.push clause }
  | .newLocal _ goal =>
    -- TODO: apply eliminators
    preprocess goal

end Preprocessor

open Preprocessor

partial def main (mvarId : MVarId) (mainDeclName : Name) : MetaM Grind.State := do
  mvarId.ensureProp
  mvarId.ensureNoMVar
  let mvarId ← mvarId.revertAll
  mvarId.ensureNoMVar
  let mvarId ← mvarId.abstractNestedProofs mainDeclName
  let mvarId ← mvarId.unfoldReducible
  let mvarId ← mvarId.betaReduce
  let s ← (preprocess { mvarId } *> getThe Grind.State) |>.run |>.run mainDeclName
  return s

end Lean.Meta.Grind

/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Intro

namespace Lean.Meta

def getCtorNumPropFields (ctorInfo : ConstructorVal) : MetaM Nat := do
  forallTelescopeReducing ctorInfo.type fun xs _ => do
    let mut numProps := 0
    for i in [:ctorInfo.numFields] do
      if (← isProp (← inferType xs[ctorInfo.numParams + i])) then
        numProps := numProps + 1
    return numProps

inductive InjectionResultCore where
  | solved
  | subgoal (mvarId : MVarId) (numNewEqs : Nat)

def injectionCore (mvarId : MVarId) (fvarId : FVarId) : MetaM InjectionResultCore :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `injection
    let decl ← getLocalDecl fvarId
    let type ← whnf decl.type
    match type.eq? with
    | none           => throwTacticEx `injection mvarId "equality expected"
    | some (α, a, b) =>
      let a ← whnf a
      let b ← whnf b
      let target ← getMVarType mvarId
      let env ← getEnv
      match a.isConstructorApp? env, b.isConstructorApp? env with
      | some aCtor, some bCtor =>
        let val ← mkNoConfusion target (mkFVar fvarId)
        if aCtor.name != bCtor.name then
          assignExprMVar mvarId val
          pure InjectionResultCore.solved
        else
          let valType ← inferType val
          let valType ← whnf valType
          match valType with
          | Expr.forallE _ newTarget _ _ =>
            let newTarget := newTarget.headBeta
            let tag ← getMVarTag mvarId
            let newMVar ← mkFreshExprSyntheticOpaqueMVar newTarget tag
            assignExprMVar mvarId (mkApp val newMVar)
            let mvarId ← tryClear newMVar.mvarId! fvarId
            /- Recall that `noConfusion` does not include equalities for
               propositions since they are trivial due to proof irrelevance. -/
            let numPropFields ← getCtorNumPropFields aCtor
            return InjectionResultCore.subgoal mvarId (aCtor.numFields - numPropFields)
          | _ => throwTacticEx `injection mvarId "ill-formed noConfusion auxiliary construction"
      | _, _ => throwTacticEx `injection mvarId "equality of constructor applications expected"

inductive InjectionResult where
  | solved
  | subgoal (mvarId : MVarId) (newEqs : Array FVarId) (remainingNames : List Name)

private def heqToEq (mvarId : MVarId) (fvarId : FVarId) (tryToClear : Bool) : MetaM (FVarId × MVarId) :=
  withMVarContext mvarId do
   let decl ← getLocalDecl fvarId
   let type ← whnf decl.type
   match type.heq? with
   | none              => pure (fvarId, mvarId)
   | some (α, a, β, b) =>
     if (← isDefEq α β) then
       let pr ← mkEqOfHEq (mkFVar fvarId)
       let eq ← mkEq a b
       let mut mvarId ← assert mvarId decl.userName eq pr
       if tryToClear then
         mvarId ← tryClear mvarId fvarId
       let (fvarId, mvarId') ← intro1P mvarId
       return (fvarId, mvarId')
     else
       return (fvarId, mvarId)

def injectionIntro (mvarId : MVarId) (numEqs : Nat) (newNames : List Name) (tryToClear := true) : MetaM InjectionResult :=
  let rec go : Nat → MVarId → Array FVarId → List Name → MetaM InjectionResult
    | 0, mvarId, fvarIds, remainingNames =>
      return InjectionResult.subgoal mvarId fvarIds remainingNames
    | n+1, mvarId, fvarIds, name::remainingNames => do
      let (fvarId, mvarId) ← intro mvarId name
      let (fvarId, mvarId) ← heqToEq mvarId fvarId tryToClear
      go n mvarId (fvarIds.push fvarId) remainingNames
    | n+1, mvarId, fvarIds, [] => do
      let (fvarId, mvarId) ← intro1 mvarId
      let (fvarId, mvarId) ← heqToEq mvarId fvarId tryToClear
      go n mvarId (fvarIds.push fvarId) []
  go numEqs mvarId #[] newNames

def injection (mvarId : MVarId) (fvarId : FVarId) (newNames : List Name := []) : MetaM InjectionResult := do
  match (← injectionCore mvarId fvarId) with
  | InjectionResultCore.solved                => pure InjectionResult.solved
  | InjectionResultCore.subgoal mvarId numEqs => injectionIntro mvarId numEqs newNames

partial def injections (mvarId : MVarId) (maxDepth : Nat := 5) : MetaM (Option MVarId) :=
  withMVarContext mvarId do
    let fvarIds := (← getLCtx).getFVarIds
    go maxDepth fvarIds.toList mvarId
where
  go : Nat → List FVarId → MVarId → MetaM (Option MVarId)
    | 0,   _,  _      => throwTacticEx `injections mvarId "recursion depth exceeded"
    | _,   [], mvarId => return mvarId
    | d+1, fvarId :: fvarIds, mvarId => do
      let cont := do
        go (d+1) fvarIds mvarId
      if let some (_, lhs, rhs) ← matchEq? (← getLocalDecl fvarId).type then
        let lhs ← whnf lhs
        let rhs ← whnf rhs
        if lhs.isNatLit && rhs.isNatLit then cont
        else
          try
            match (← injection mvarId fvarId) with
            | InjectionResult.solved  => return none
            | InjectionResult.subgoal mvarId newEqs _ =>
              withMVarContext mvarId <| go d (newEqs.toList ++ fvarIds) mvarId
          catch _ => cont
      else cont

end Lean.Meta

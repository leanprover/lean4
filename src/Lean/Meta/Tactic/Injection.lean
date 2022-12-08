/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Subst
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Intro

namespace Lean.Meta

def getCtorNumPropFields (ctorInfo : ConstructorVal) : MetaM Nat := do
  forallTelescopeReducing ctorInfo.type fun xs _ => do
    let mut numProps := 0
    for i in [:ctorInfo.numFields] do
      if (← isProp (← inferType xs[ctorInfo.numParams + i]!)) then
        numProps := numProps + 1
    return numProps

inductive InjectionResultCore where
  | solved
  | subgoal (mvarId : MVarId) (numNewEqs : Nat)

def injectionCore (mvarId : MVarId) (fvarId : FVarId) : MetaM InjectionResultCore :=
  mvarId.withContext do
    mvarId.checkNotAssigned `injection
    let decl ← fvarId.getDecl
    let type ← whnf decl.type
    let go (type prf : Expr) : MetaM InjectionResultCore := do
      match type.eq? with
      | none           => throwTacticEx `injection mvarId "equality expected"
      | some (_, a, b) =>
        let a ← whnf a
        let b ← whnf b
        let target ← mvarId.getType
        let env ← getEnv
        match a.isConstructorApp? env, b.isConstructorApp? env with
        | some aCtor, some bCtor =>
          let val ← mkNoConfusion target prf
          if aCtor.name != bCtor.name then
            mvarId.assign val
            return InjectionResultCore.solved
          else
            let valType ← inferType val
            let valType ← whnf valType
            match valType with
            | Expr.forallE _ newTarget _ _ =>
              let newTarget := newTarget.headBeta
              let tag ← mvarId.getTag
              let newMVar ← mkFreshExprSyntheticOpaqueMVar newTarget tag
              mvarId.assign (mkApp val newMVar)
              let mvarId ← newMVar.mvarId!.tryClear fvarId
              /- Recall that `noConfusion` does not include equalities for
                 propositions since they are trivial due to proof irrelevance. -/
              let numPropFields ← getCtorNumPropFields aCtor
              return InjectionResultCore.subgoal mvarId (aCtor.numFields - numPropFields)
            | _ => throwTacticEx `injection mvarId "ill-formed noConfusion auxiliary construction"
        | _, _ => throwTacticEx `injection mvarId "equality of constructor applications expected"
    let prf := mkFVar fvarId
    if let some (α, a, β, b) := type.heq? then
      if (← isDefEq α β) then
        go (← mkEq a b) (← mkEqOfHEq prf)
      else
        go type prf
    else
      go type prf

inductive InjectionResult where
  | solved
  | subgoal (mvarId : MVarId) (newEqs : Array FVarId) (remainingNames : List Name)


def injectionIntro (mvarId : MVarId) (numEqs : Nat) (newNames : List Name) (tryToClear := true) : MetaM InjectionResult :=
  let rec go : Nat → MVarId → Array FVarId → List Name → MetaM InjectionResult
    | 0, mvarId, fvarIds, remainingNames =>
      return InjectionResult.subgoal mvarId fvarIds remainingNames
    | n+1, mvarId, fvarIds, name::remainingNames => do
      let (fvarId, mvarId) ← mvarId.intro name
      let (fvarId, mvarId) ← heqToEq mvarId fvarId tryToClear
      go n mvarId (fvarIds.push fvarId) remainingNames
    | n+1, mvarId, fvarIds, [] => do
      let (fvarId, mvarId) ← mvarId.intro1
      let (fvarId, mvarId) ← heqToEq mvarId fvarId tryToClear
      go n mvarId (fvarIds.push fvarId) []
  go numEqs mvarId #[] newNames

def injection (mvarId : MVarId) (fvarId : FVarId) (newNames : List Name := []) : MetaM InjectionResult := do
  match (← injectionCore mvarId fvarId) with
  | .solved                => pure .solved
  | .subgoal mvarId numEqs => injectionIntro mvarId numEqs newNames

inductive InjectionsResult where
  | solved
  | subgoal (mvarId : MVarId) (remainingNames : List Name)

partial def injections (mvarId : MVarId) (newNames : List Name := []) (maxDepth : Nat := 5) : MetaM InjectionsResult :=
  mvarId.withContext do
    let fvarIds := (← getLCtx).getFVarIds
    go maxDepth fvarIds.toList mvarId newNames
where
  go : Nat → List FVarId → MVarId → List Name → MetaM InjectionsResult
    | 0,   _,  _,      _        => throwTacticEx `injections mvarId "recursion depth exceeded"
    | _,   [], mvarId, newNames => return .subgoal mvarId newNames
    | d+1, fvarId :: fvarIds, mvarId, newNames => do
      let cont := do
        go (d+1) fvarIds mvarId newNames
      if let some (_, lhs, rhs) ← matchEqHEq? (← fvarId.getType) then
        let lhs ← whnf lhs
        let rhs ← whnf rhs
        if lhs.isNatLit && rhs.isNatLit then cont
        else
          try
            match (← injection mvarId fvarId newNames) with
            | .solved  => return .solved
            | .subgoal mvarId newEqs remainingNames =>
              mvarId.withContext <| go d (newEqs.toList ++ fvarIds) mvarId remainingNames
          catch _ => cont
      else cont

end Lean.Meta

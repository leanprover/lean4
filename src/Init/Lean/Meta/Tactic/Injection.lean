/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.AppBuilder
import Init.Lean.Meta.Tactic.Clear
import Init.Lean.Meta.Tactic.Assert
import Init.Lean.Meta.Tactic.Intro

namespace Lean
namespace Meta

inductive InjectionResultCore
| solved
| subgoal (mvarId : MVarId) (numNewEqs : Nat)

private def getConstructorVal (ctorName : Name) (numArgs : Nat) : MetaM (Option ConstructorVal) := do
env ← getEnv;
match env.find? ctorName with
| some (ConstantInfo.ctorInfo v) => if numArgs == v.nparams + v.nfields then pure (some v) else pure none
| _                              => pure none

def constructorApp? (e : Expr) : MetaM (Option ConstructorVal) := do
match e with
| Expr.lit (Literal.natVal n) _ =>
  if n == 0 then getConstructorVal `Nat.zero 0 else getConstructorVal `Nat.succ 1
| _ =>
  match e.getAppFn with
  | Expr.const n _ _ => getConstructorVal n e.getAppNumArgs
  | _                => pure none

def injectionCore (mvarId : MVarId) (fvarId : FVarId) : MetaM InjectionResultCore := do
withMVarContext mvarId $ do
  checkNotAssigned mvarId `injection;
  decl ← getLocalDecl fvarId;
  type ← whnf decl.type;
  match type.eq? with
  | none           => throwTacticEx `injection mvarId "equality expected"
  | some (α, a, b) => do
    a ← whnf a;
    b ← whnf b;
    target ← getMVarType mvarId;
    aCtor? ← constructorApp? a;
    bCtor? ← constructorApp? b;
    match aCtor?, bCtor? with
    | some aCtor, some bCtor => do
      val ← mkNoConfusion target (mkFVar fvarId);
      if aCtor.name != bCtor.name then do
        assignExprMVar mvarId val;
        pure InjectionResultCore.solved
      else do
        valType ← inferType val;
        valType ← whnf valType;
        match valType with
        | Expr.forallE _ newTarget _ _ =>  do
          let newTarget := newTarget.headBeta;
          tag ← getMVarTag mvarId;
          newMVar ← mkFreshExprSyntheticOpaqueMVar newTarget tag;
          assignExprMVar mvarId (mkApp val newMVar);
          mvarId ← tryClear newMVar.mvarId! fvarId;
          pure $ InjectionResultCore.subgoal mvarId aCtor.nfields
        | _ => throwTacticEx `injection mvarId "ill-formed noConfusion auxiliary construction"
    | _, _ => throwTacticEx `injection mvarId "equality of constructor applications expected"

inductive InjectionResult
| solved
| subgoal (mvarId : MVarId) (newEqs : Array FVarId) (remainingNames : List Name)

def injection (mvarId : MVarId) (fvarId : FVarId) (newNames : List Name := []) (useUnusedNames : Bool := true) : MetaM InjectionResult := do
r ← injectionCore mvarId fvarId;
match r with
| InjectionResultCore.solved => pure InjectionResult.solved
| InjectionResultCore.subgoal mvarId numEqs => do
  (fvarIds, mvarId) ← introN mvarId numEqs newNames useUnusedNames;
  pure $ InjectionResult.subgoal mvarId fvarIds (newNames.drop numEqs)

end Meta
end Lean

/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.AppBuilder
import Init.Lean.Meta.Tactic.Util
import Init.Lean.Meta.Tactic.Assert

namespace Lean
namespace Meta

inductive InjectionResult
| solved
| subgoal (mvarId : MVarId) (numNewEqs : Nat)

def constructorApp? (e : Expr) : MetaM (Option ConstructorVal) := do
let f     := e.getAppFn;
let nargs := e.getAppNumArgs;
env ← getEnv;
matchConst env f (fun _ => pure none) $ fun cinfo _ =>
match cinfo with
| ConstantInfo.ctorInfo v => if e.getAppNumArgs == v.nparams + v.nfields then pure (some v) else pure none
| _                       => pure none

def injectionCore (mvarId : MVarId) (fvarId : FVarId) : MetaM InjectionResult := do
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
        pure InjectionResult.solved
      else do
        valType ← inferType val;
        valType ← whnf valType;
        match valType with
        | Expr.forallE _ newTarget _ _ =>  do
          let newTarget := newTarget.headBeta;
          tag ← getMVarTag mvarId;
          newMVar ← mkFreshExprSyntheticOpaqueMVar newTarget tag;
          assignExprMVar mvarId (mkApp val newMVar);
          pure $ InjectionResult.subgoal newMVar.mvarId! aCtor.nfields
        | _ => throwTacticEx `injection mvarId "ill-formed noConfusion auxiliary construction"
    | _, _ => throwTacticEx `injection mvarId "equality of constructor applications expected"

end Meta
end Lean

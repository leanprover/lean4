/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Tactic.Replace

namespace Lean.Meta

/- Low-level delta expansion. It is used to implement equation lemmas and elimination principles for recursive definitions. -/
def deltaExpand (e : Expr) (p : Name → Bool) : CoreM Expr :=
  Core.transform e fun e =>
    matchConst e.getAppFn (fun _ => return TransformStep.visit e) fun fInfo fLvls => do
      if p fInfo.name && fInfo.hasValue && fInfo.lparams.length == fLvls.length then
        let f := fInfo.instantiateValueLevelParams fLvls
        return TransformStep.visit (f.betaRev e.getAppRevArgs)
      else
        return TransformStep.visit e

def deltaTarget (mvarId : MVarId) (p : Name → Bool) : MetaM MVarId :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `delta
    change mvarId (← deltaExpand (← getMVarType mvarId) p) (checkDefEq := false)

def deltaLocalDecl (mvarId : MVarId) (fvarId : FVarId) (p : Name → Bool) : MetaM MVarId :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `delta
    let localDecl ← getLocalDecl fvarId
    changeLocalDecl mvarId fvarId (← deltaExpand (← getMVarType mvarId) p) (checkDefEq := false)

end Lean.Meta

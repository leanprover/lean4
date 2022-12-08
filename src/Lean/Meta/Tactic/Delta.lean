/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Meta.Tactic.Replace

namespace Lean.Meta

def delta? (e : Expr) (p : Name → Bool := fun _ => true) : CoreM (Option Expr) :=
  matchConst e.getAppFn (fun _ => return none) fun fInfo fLvls => do
    if p fInfo.name && fInfo.hasValue && fInfo.levelParams.length == fLvls.length then
      let f ← instantiateValueLevelParams fInfo fLvls
      return some (f.betaRev e.getAppRevArgs (useZeta := true))
    else
      return none

/-- Low-level delta expansion. It is used to implement equation lemmas and elimination principles for recursive definitions. -/
def deltaExpand (e : Expr) (p : Name → Bool) : CoreM Expr :=
  Core.transform e fun e => do
    match (← delta? e p) with
    | some e' => return .visit e'
    | none    => return .continue

/--
Delta expand declarations that satisfy `p` at `mvarId` type.
-/
def _root_.Lean.MVarId.deltaTarget (mvarId : MVarId) (p : Name → Bool) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `delta
    mvarId.change (← deltaExpand (← mvarId.getType) p) (checkDefEq := false)

@[deprecated MVarId.deltaTarget]
def deltaTarget (mvarId : MVarId) (p : Name → Bool) : MetaM MVarId :=
  mvarId.deltaTarget p

/--
Delta expand declarations that satisfy `p` at `fvarId` type.
-/
def _root_.Lean.MVarId.deltaLocalDecl (mvarId : MVarId) (fvarId : FVarId) (p : Name → Bool) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `delta
    mvarId.changeLocalDecl fvarId (← deltaExpand (← mvarId.getType) p) (checkDefEq := false)

@[deprecated MVarId.deltaLocalDecl]
def deltaLocalDecl (mvarId : MVarId) (fvarId : FVarId) (p : Name → Bool) : MetaM MVarId :=
  mvarId.deltaLocalDecl fvarId p

end Lean.Meta

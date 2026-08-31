/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Replace
import Lean.Meta.Transform
public section
namespace Lean.Meta

def delta? (e : Expr) (p : Name → Bool := fun _ => true) (allowOpaque := false) : CoreM (Option Expr) :=
  matchConst e.getAppFn (fun _ => return none) fun fInfo fLvls => do
    if p fInfo.name && fInfo.hasValue (allowOpaque := allowOpaque) && fInfo.levelParams.length == fLvls.length then
      let f ← instantiateValueLevelParams fInfo fLvls (allowOpaque := allowOpaque)
      return some (f.betaRev e.getAppRevArgs (useZeta := true))
    else
      return none

/-- Low-level delta expansion. It is used to implement equation lemmas and elimination principles for recursive definitions. -/
def deltaExpand (e : Expr) (p : Name → Bool) (allowOpaque := false) : CoreM Expr :=
  Core.transform e fun e => do
    match (← delta? e p (allowOpaque := allowOpaque)) with
    | some e' => return .visit e'
    | none    => return .continue

/--
Delta expand declarations that satisfy `p` at `mvarId` type.
-/
def _root_.Lean.MVarId.deltaTarget (mvarId : MVarId) (p : Name → Bool) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `delta
    mvarId.change (← deltaExpand (← mvarId.getType) p) (checkDefEq := false)

/--
Delta expand declarations that satisfy `p` at `fvarId` type.
-/
def _root_.Lean.MVarId.deltaLocalDecl (mvarId : MVarId) (fvarId : FVarId) (p : Name → Bool) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `delta
    mvarId.changeLocalDecl fvarId (← deltaExpand (← fvarId.getType) p) (checkDefEq := false)

end Lean.Meta

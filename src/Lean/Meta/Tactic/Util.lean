/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExpr
import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.LevelDefEq
import Lean.Meta.PPGoal

namespace Lean.Meta

/-- Aka user name -/
def getMVarTag (mvarId : MVarId) : MetaM Name := do
  let mvarDecl ← getMVarDecl mvarId
  pure mvarDecl.userName

def setMVarTag (mvarId : MVarId) (tag : Name) : MetaM Unit := do
  modify fun s => { s with mctx := s.mctx.setMVarUserName mvarId tag }

def appendTag (tag : Name) (suffix : Name) : Name :=
  let view := extractMacroScopes tag
  let view := { view with name := view.name ++ suffix.eraseMacroScopes }
  view.review

def appendTagSuffix (mvarId : MVarId) (suffix : Name) : MetaM Unit := do
  let tag ← getMVarTag mvarId
  setMVarTag mvarId (appendTag tag suffix)

def mkFreshExprSyntheticOpaqueMVar (type : Expr) (tag : Name := Name.anonymous) : MetaM Expr :=
  mkFreshExprMVar type MetavarKind.syntheticOpaque tag

def throwTacticEx {α} (tacticName : Name) (mvarId : MVarId) (msg : MessageData) (ref := Syntax.missing) : MetaM α :=
  throwError "tactic '{tacticName}' failed, {msg}\n{MessageData.ofGoal mvarId}"

def checkNotAssigned (mvarId : MVarId) (tacticName : Name) : MetaM Unit := do
  if (← isExprMVarAssigned mvarId) then
    throwTacticEx tacticName mvarId "metavariable has already been assigned"

def getMVarType (mvarId : MVarId) : MetaM Expr := do
  pure (← getMVarDecl mvarId).type

def getMVarType' (mvarId : MVarId) : MetaM Expr := do
  whnf (← instantiateMVars (← getMVarDecl mvarId).type)

builtin_initialize registerTraceClass `Meta.Tactic

/-- Assign `mvarId` to `sorryAx` -/
def admit (mvarId : MVarId) (synthetic := true) : MetaM Unit :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `admit
    let mvarType ← getMVarType mvarId
    let val ← mkSorry mvarType synthetic
    assignExprMVar mvarId val

/-- Beta reduce the metavariable type head -/
def headBetaMVarType (mvarId : MVarId) : MetaM Unit := do
  setMVarType mvarId (← getMVarType mvarId).headBeta

/-- Collect nondependent hypotheses. -/
def getNondepPropHyps (mvarId : MVarId) : MetaM (Array FVarId) :=
  withMVarContext mvarId do
    let mut candidates : NameHashSet := {}
    for localDecl in (← getLCtx) do
      candidates ← removeDeps localDecl.type candidates
      match localDecl.value? with
      | none => pure ()
      | some value => candidates ← removeDeps value candidates
      if (← isProp localDecl.type) && !localDecl.hasValue then
        candidates := candidates.insert localDecl.fvarId
    candidates ← removeDeps (← getMVarType mvarId) candidates
    if candidates.isEmpty then
      return #[]
    else
      let mut result := #[]
      for localDecl in (← getLCtx) do
        if candidates.contains localDecl.fvarId then
          result := result.push localDecl.fvarId
      return result
where
  removeDeps (e : Expr) (candidates : NameHashSet) : MetaM NameHashSet := do
    let e ← instantiateMVars e
    let visit : StateRefT NameHashSet MetaM NameHashSet := do
      e.forEach fun
        | Expr.fvar fvarId _ => modify fun s => s.erase fvarId
        | _ => pure ()
      get
    visit |>.run' candidates

end Lean.Meta

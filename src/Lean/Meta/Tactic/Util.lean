/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExprWhere
import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.PPGoal

namespace Lean.Meta

/-- Get the user name of the given metavariable. -/
def _root_.Lean.MVarId.getTag (mvarId : MVarId) : MetaM Name :=
  return (← mvarId.getDecl).userName

@[deprecated MVarId.getTag]
def getMVarTag (mvarId : MVarId) : MetaM Name :=
  mvarId.getTag

def _root_.Lean.MVarId.setTag (mvarId : MVarId) (tag : Name) : MetaM Unit := do
  modify fun s => { s with mctx := s.mctx.setMVarUserName mvarId tag }

@[deprecated MVarId.setTag]
def setMVarTag (mvarId : MVarId) (tag : Name) : MetaM Unit := do
  mvarId.setTag tag

def appendTag (tag : Name) (suffix : Name) : Name :=
  tag.modifyBase (· ++ suffix.eraseMacroScopes)

def appendTagSuffix (mvarId : MVarId) (suffix : Name) : MetaM Unit := do
  let tag ← mvarId.getTag
  mvarId.setTag (appendTag tag suffix)

def mkFreshExprSyntheticOpaqueMVar (type : Expr) (tag : Name := Name.anonymous) : MetaM Expr :=
  mkFreshExprMVar type MetavarKind.syntheticOpaque tag

def throwTacticEx (tacticName : Name) (mvarId : MVarId) (msg : MessageData) : MetaM α :=
  if msg.isEmpty then
    throwError "tactic '{tacticName}' failed\n{mvarId}"
  else
    throwError "tactic '{tacticName}' failed, {msg}\n{mvarId}"

def throwNestedTacticEx {α} (tacticName : Name) (ex : Exception) : MetaM α := do
  throwError "tactic '{tacticName}' failed, nested error:\n{ex.toMessageData}"

/-- Throw a tactic exception with given tactic name if the given metavariable is assigned. -/
def _root_.Lean.MVarId.checkNotAssigned (mvarId : MVarId) (tacticName : Name) : MetaM Unit := do
  if (← mvarId.isAssigned) then
    throwTacticEx tacticName mvarId "metavariable has already been assigned"

@[deprecated MVarId.checkNotAssigned]
def checkNotAssigned (mvarId : MVarId) (tacticName : Name) : MetaM Unit := do
  mvarId.checkNotAssigned tacticName

/-- Get the type the given metavariable. -/
def _root_.Lean.MVarId.getType (mvarId : MVarId) : MetaM Expr :=
  return (← mvarId.getDecl).type

@[deprecated MVarId.getType]
def getMVarType (mvarId : MVarId) : MetaM Expr :=
  mvarId.getType

/-- Get the type the given metavariable after instantiating metavariables and reducing to
weak head normal form. -/
-- The `instantiateMVars` needs to be on the outside,
-- since `whnf` can unfold local definitions which may introduce metavariables.
-- We don't need an `instantiateMVars` before the `whnf`, since it instantiates as necessary.
def _root_.Lean.MVarId.getType' (mvarId : MVarId) : MetaM Expr := do
  instantiateMVars (← whnf (← mvarId.getType))

@[deprecated MVarId.getType']
def getMVarType' (mvarId : MVarId) : MetaM Expr := do
  mvarId.getType'

builtin_initialize registerTraceClass `Meta.Tactic

/-- Assign `mvarId` to `sorryAx` -/
def _root_.Lean.MVarId.admit (mvarId : MVarId) (synthetic := true) : MetaM Unit :=
  mvarId.withContext do
    mvarId.checkNotAssigned `admit
    let mvarType ← mvarId.getType
    let val ← mkSorry mvarType synthetic
    mvarId.assign val

@[deprecated MVarId.admit]
def admit (mvarId : MVarId) (synthetic := true) : MetaM Unit :=
  mvarId.admit synthetic

/-- Beta reduce the metavariable type head -/
def _root_.Lean.MVarId.headBetaType (mvarId : MVarId) : MetaM Unit := do
  mvarId.setType (← mvarId.getType).headBeta

@[deprecated MVarId.headBetaType]
def headBetaMVarType (mvarId : MVarId) : MetaM Unit := do
  mvarId.headBetaType

/-- Collect nondependent hypotheses that are propositions. -/
def _root_.Lean.MVarId.getNondepPropHyps (mvarId : MVarId) : MetaM (Array FVarId) :=
  let removeDeps (e : Expr) (candidates : FVarIdHashSet) : MetaM FVarIdHashSet := do
    let e ← instantiateMVars e
    let visit : StateRefT FVarIdHashSet MetaM FVarIdHashSet := do
      e.forEachWhere Expr.isFVar fun e => modify fun s => s.erase e.fvarId!
      get
    visit |>.run' candidates
  mvarId.withContext do
    let mut candidates : FVarIdHashSet := {}
    for localDecl in (← getLCtx) do
      unless localDecl.isImplementationDetail do
        candidates ← removeDeps localDecl.type candidates
        match localDecl.value? with
        | none => pure ()
        | some value => candidates ← removeDeps value candidates
        if (← isProp localDecl.type) && !localDecl.hasValue then
          candidates := candidates.insert localDecl.fvarId
    candidates ← removeDeps (← mvarId.getType) candidates
    if candidates.isEmpty then
      return #[]
    else
      let mut result := #[]
      for localDecl in (← getLCtx) do
        if candidates.contains localDecl.fvarId then
          result := result.push localDecl.fvarId
      return result

@[deprecated MVarId.getNondepPropHyps]
def getNondepPropHyps (mvarId : MVarId) : MetaM (Array FVarId) :=
  mvarId.getNondepPropHyps

partial def saturate (mvarId : MVarId) (x : MVarId → MetaM (Option (List MVarId))) : MetaM (List MVarId) := do
  let (_, r) ← go mvarId |>.run #[]
  return r.toList
where
  go (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit :=
    withIncRecDepth do
      match (← x mvarId) with
      | none => modify fun s => s.push mvarId
      | some mvarIds => mvarIds.forM go

def exactlyOne (mvarIds : List MVarId) (msg : MessageData := "unexpected number of goals") : MetaM MVarId :=
  match mvarIds with
  | [mvarId] => return mvarId
  | _        => throwError msg

def ensureAtMostOne (mvarIds : List MVarId) (msg : MessageData := "unexpected number of goals") : MetaM (Option MVarId) :=
  match mvarIds with
  | []       => return none
  | [mvarId] => return some mvarId
  | _        => throwError msg

/-- Return all propositions in the local context. -/
def getPropHyps : MetaM (Array FVarId) := do
  let mut result := #[]
  for localDecl in (← getLCtx) do
    unless localDecl.isImplementationDetail do
      if (← isProp localDecl.type) then
        result := result.push localDecl.fvarId
  return result

def _root_.Lean.MVarId.inferInstance (mvarId : MVarId) : MetaM Unit := mvarId.withContext do
  mvarId.checkNotAssigned `infer_instance
  let synthVal ← synthInstance (← mvarId.getType)
  unless (← isDefEq (mkMVar mvarId) synthVal) do
    throwTacticEx `infer_instance mvarId "`infer_instance` tactic failed to assign instance"

inductive TacticResultCNM where
  | closed
  | noChange
  | modified (mvarId : MVarId)

end Lean.Meta

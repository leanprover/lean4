#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.LevelDefEq

namespace Lean.Meta

/-- Aka user name -/
def getMVarTag (mvarId : MVarId) : MetaM Name := do
let mvarDecl ← getMVarDecl mvarId
pure mvarDecl.userName

def setMVarTag (mvarId : MVarId) (tag : Name) : MetaM Unit := do
modify $ fun s => { s with mctx := s.mctx.setMVarUserName mvarId tag }

def appendTag (tag : Name) (suffix : Name) : Name :=
let view := extractMacroScopes tag
let view := { view with name := view.name ++ suffix.eraseMacroScopes }
view.review

def appendTagSuffix (mvarId : MVarId) (suffix : Name) : MetaM Unit := do
let tag ← getMVarTag mvarId
setMVarTag mvarId (appendTag tag suffix)

def mkFreshExprSyntheticOpaqueMVar (type : Expr) (userName : Name := Name.anonymous) : MetaM Expr :=
mkFreshExprMVar type MetavarKind.syntheticOpaque userName

def throwTacticEx {α} (tacticName : Name) (mvarId : MVarId) (msg : MessageData) (ref := Syntax.missing) : MetaM α :=
throwError! "tactic '{tacticName}' failed, {msg}\n{MessageData.ofGoal mvarId}"

def checkNotAssigned (mvarId : MVarId) (tacticName : Name) : MetaM Unit := do
if (← isExprMVarAssigned mvarId) then
  throwTacticEx tacticName mvarId "metavariable has already been assigned"

def getMVarType (mvarId : MVarId) : MetaM Expr := do
let mvarDecl ← getMVarDecl mvarId
pure mvarDecl.type

def ppGoal (mvarId : MVarId) : MetaM Format := do
liftIO $ Lean.ppGoal { env := (← getEnv), mctx := (← getMCtx), opts := (← getOptions) } mvarId

builtin_initialize registerTraceClass `Meta.Tactic

/-- Assign `mvarId` to `sorryAx` -/
def admit (mvarId : MVarId) (synthetic := true) : MetaM Unit :=
withMVarContext mvarId do
  checkNotAssigned mvarId `admit
  let mvarType ← getMVarType mvarId
  let val ← mkSorry mvarType synthetic
  assignExprMVar mvarId val

end Lean.Meta

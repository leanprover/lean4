/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic
import Lean.Meta.AppBuilder
import Lean.Meta.LevelDefEq

namespace Lean
namespace Meta

/-- Aka user name -/
def getMVarTag (mvarId : MVarId) : MetaM Name := do
mvarDecl ← getMVarDecl mvarId;
pure mvarDecl.userName

def setMVarTag (mvarId : MVarId) (tag : Name) : MetaM Unit := do
modify $ fun s => { s with mctx := s.mctx.setMVarUserName mvarId tag }

def appendTag (tag : Name) (suffix : Name) : Name :=
let view := extractMacroScopes tag;
let view := { view with name := view.name ++ suffix.eraseMacroScopes };
view.review

def appendTagSuffix (mvarId : MVarId) (suffix : Name) : MetaM Unit := do
tag ← getMVarTag mvarId;
setMVarTag mvarId (appendTag tag suffix)

def mkFreshExprSyntheticOpaqueMVar (type : Expr) (userName : Name := Name.anonymous) : MetaM Expr :=
mkFreshExprMVar type MetavarKind.syntheticOpaque userName

def throwTacticEx {α} (tacticName : Name) (mvarId : MVarId) (msg : MessageData) (ref := Syntax.missing) : MetaM α :=
throwError $ "tactic '" ++ tacticName ++ "' failed, " ++ msg ++ Format.line ++ MessageData.ofGoal mvarId

def checkNotAssigned (mvarId : MVarId) (tacticName : Name) : MetaM Unit :=
whenM (isExprMVarAssigned mvarId) $ throwTacticEx tacticName mvarId "metavariable has already been assigned"

def getMVarType (mvarId : MVarId) : MetaM Expr := do
mvarDecl ← getMVarDecl mvarId;
pure mvarDecl.type

def ppGoal (mvarId : MVarId) : MetaM Format := do
env  ← getEnv;
mctx ← getMCtx;
opts ← getOptions;
pure $ ppGoal env mctx opts mvarId

@[init] private def regTraceClasses : IO Unit :=
registerTraceClass `Meta.Tactic

/-- Assign `mvarId` to `sorryAx` -/
def admit (mvarId : MVarId) (synthetic := true) : MetaM Unit :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `admit;
  mvarType ← getMVarType mvarId;
  val ← mkSorry mvarType synthetic;
  assignExprMVar mvarId val;
  pure ()

end Meta
end Lean

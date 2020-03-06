/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic
import Init.Lean.Meta.LevelDefEq

namespace Lean
namespace Meta

/-- Aka user name -/
def getMVarTag (mvarId : MVarId) : MetaM Name := do
mvarDecl ← getMVarDecl mvarId;
pure mvarDecl.userName

def setMVarTag (mvarId : MVarId) (tag : Name) : MetaM Unit := do
modify $ fun s => { mctx := s.mctx.setMVarUserName mvarId tag, .. s }

def mkFreshExprSyntheticOpaqueMVar (type : Expr) (userName : Name := Name.anonymous) : MetaM Expr :=
mkFreshExprMVar type userName MetavarKind.syntheticOpaque

def throwTacticEx {α} (tacticName : Name) (mvarId : MVarId) (msg : MessageData) : MetaM α := do
throwEx $ fun ctx => Exception.tactic tacticName mvarId (MessageData.withContext ctx msg) ctx

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

@[inline] protected def orelse {α} (x y : MetaM α) : MetaM α := do
s ← get; catch x (fun _ => do restore s.env s.mctx s.postponed; y)

instance Meta.hasOrelse {α} : HasOrelse (MetaM α) := ⟨Meta.orelse⟩

@[init] private def regTraceClasses : IO Unit :=
registerTraceClass `Meta.Tactic

end Meta
end Lean

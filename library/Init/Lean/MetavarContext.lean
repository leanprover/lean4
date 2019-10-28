/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.AbstractMetavarContext

namespace Lean

structure MetavarContext :=
(decls       : PersistentHashMap Name MetavarDecl := {})
(lAssignment : PersistentHashMap Name Level := {})
(eAssignment : PersistentHashMap Name Expr := {})
(dAssignment : PersistentHashMap Name DelayedMetavarAssignment := {})

namespace MetavarContext

@[export lean_mk_metavar_ctx]
def mkMetavarContext : Unit → MetavarContext :=
fun _ => {}

/- Low level API for creating metavariable declarations.
   It is used to implement actions in the monads `Elab` and `Tactic`.
   It should not be used directly since the argument `(mvarId : Name)` is assumed to be "unique". -/
@[export lean_metavar_ctx_mk_decl]
def mkDecl (m : MetavarContext) (mvarId : Name) (userName : Name) (lctx : LocalContext) (type : Expr) (synthetic : Bool := false) : MetavarContext :=
{ decls := m.decls.insert mvarId { userName := userName, lctx := lctx, type := type, synthetic := synthetic }, .. m }

@[export lean_metavar_ctx_find_decl]
def findDecl (m : MetavarContext) (mvarId : Name) : Option MetavarDecl :=
m.decls.find mvarId

def getDecl (m : MetavarContext) (mvarId : Name) : MetavarDecl :=
match m.decls.find mvarId with
| some decl => decl
| none      => panic! "unknown metavariable"

@[export lean_metavar_ctx_assign_level]
def assignLevel (m : MetavarContext) (mvarId : Name) (val : Level) : MetavarContext :=
{ lAssignment := m.lAssignment.insert mvarId val, .. m }

@[export lean_metavar_ctx_assign_expr]
def assignExpr (m : MetavarContext) (mvarId : Name) (val : Expr) : MetavarContext :=
{ eAssignment := m.eAssignment.insert mvarId val, .. m }

@[export lean_metavar_ctx_assign_delayed]
def assignDelayed (m : MetavarContext) (mvarId : Name) (lctx : LocalContext) (fvars : Array Expr) (val : Expr) : MetavarContext :=
{ dAssignment := m.dAssignment.insert mvarId { lctx := lctx, fvars := fvars, val := val }, .. m }

@[export lean_metavar_ctx_get_level_assignment]
def getLevelAssignment (m : MetavarContext) (mvarId : Name) : Option Level :=
m.lAssignment.find mvarId

@[export lean_metavar_ctx_get_expr_assignment]
def getExprAssignment (m : MetavarContext) (mvarId : Name) : Option Expr :=
m.eAssignment.find mvarId

@[export lean_metavar_ctx_get_delayed_assignment]
def getDelayedAssignment (m : MetavarContext) (mvarId : Name) : Option DelayedMetavarAssignment :=
m.dAssignment.find mvarId

@[export lean_metavar_ctx_is_level_assigned]
def isLevelAssigned (m : MetavarContext) (mvarId : Name) : Bool :=
m.lAssignment.contains mvarId

@[export lean_metavar_ctx_is_expr_assigned]
def isExprAssigned (m : MetavarContext) (mvarId : Name) : Bool :=
m.eAssignment.contains mvarId

@[export lean_metavar_ctx_is_delayed_assigned]
def isDelayedAssigned (m : MetavarContext) (mvarId : Name) : Bool :=
m.dAssignment.contains mvarId

@[export lean_metavar_ctx_erase_delayed]
def eraseDelayed (m : MetavarContext) (mvarId : Name) : MetavarContext :=
{ dAssignment := m.dAssignment.erase mvarId, .. m }

/- Remark: the following instance assumes all metavariables can be updated. -/
instance metavarContextIsAbstractMetavarContext : AbstractMetavarContext MetavarContext :=
{ empty                := {},
  isReadOnlyLevelMVar  := fun _ _ => false,
  getLevelAssignment   := MetavarContext.getLevelAssignment,
  assignLevel          := MetavarContext.assignLevel,
  isReadOnlyExprMVar   := fun _ _ => false,
  getExprAssignment    := MetavarContext.getExprAssignment,
  assignExpr           := MetavarContext.assignExpr,
  getDecl              := MetavarContext.getDecl,
  assignDelayed        := MetavarContext.assignDelayed,
  getDelayedAssignment := MetavarContext.getDelayedAssignment,
  eraseDelayed         := MetavarContext.eraseDelayed,
  mkAuxMVar            := fun mctx mvarId lctx type synthetic => some (MetavarContext.mkDecl mctx mvarId Name.anonymous lctx type synthetic)
}

/-- Return `true` iff `lvl` contains assigned level metavariables -/
@[inline] def hasAssignedLevelMVar (m : MetavarContext) (lvl : Level) : Bool :=
AbstractMetavarContext.hasAssignedLevelMVar m lvl

/-- Return `true` iff `e` contains assigned (level/expr) metavariables -/
@[inline] def hasAssignedMVar (m : MetavarContext) (e : Expr) : Bool :=
AbstractMetavarContext.hasAssignedMVar m e

@[inline] def instantiateLevelMVars (m : MetavarContext) (lvl : Level) : Level × MetavarContext :=
AbstractMetavarContext.instantiateLevelMVars lvl m

@[inline] def instantiateMVars (m : MetavarContext) (e : Expr) : Expr × MetavarContext :=
AbstractMetavarContext.instantiateMVars e m

@[inline] def mkLambda (m : MetavarContext) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr)
                       : Except MkBindingException (MetavarContext × NameGenerator × Expr) :=
AbstractMetavarContext.mkLambda m ngen lctx xs e

@[inline] def mkForall (m : MetavarContext) (ngen : NameGenerator) (lctx : LocalContext) (xs : Array Expr) (e : Expr)
                       : Except MkBindingException (MetavarContext × NameGenerator × Expr) :=
AbstractMetavarContext.mkForall m ngen lctx xs e

end MetavarContext
end Lean

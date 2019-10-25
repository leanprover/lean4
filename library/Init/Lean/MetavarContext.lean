/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.LocalContext

namespace Lean

structure MetavarDecl :=
(userName : Name)
(lctx     : LocalContext)
(type     : Expr)

/-
A delayed assignment for a metavariable `?m`. It represents an assignment of the form
`?m := (fun fvars => val)`. The local context `lctx` provides the declarations for `fvars`.
Note that `fvars` may not be defined in the local context for `?m`.
-/
structure DelayedMetavarAssignment :=
(lctx     : LocalContext)
(fvars    : List Expr)
(val      : Expr)

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
def mkDecl (m : MetavarContext) (mvarId : Name) (userName : Name) (lctx : LocalContext) (type : Expr) : MetavarContext :=
{ decls := m.decls.insert mvarId { userName := userName, lctx := lctx, type := type }, .. m }

@[export lean_metavar_ctx_find_decl]
def findDecl (m : MetavarContext) (mvarId : Name) : Option MetavarDecl :=
m.decls.find mvarId

@[inline] def getExprMVarLCtx (m : MetavarContext) (mvarId : Name) : Option LocalContext :=
MetavarDecl.lctx <$> findDecl m mvarId

@[inline] def getExprMVarType (m : MetavarContext) (mvarId : Name) : Option Expr :=
MetavarDecl.type <$> findDecl m mvarId

@[export lean_metavar_ctx_assign_level]
def assignLevel (m : MetavarContext) (mvarId : Name) (val : Level) : MetavarContext :=
{ lAssignment := m.lAssignment.insert mvarId val, .. m }

@[export lean_metavar_ctx_assign_expr]
def assignExpr (m : MetavarContext) (mvarId : Name) (val : Expr) : MetavarContext :=
{ eAssignment := m.eAssignment.insert mvarId val, .. m }

@[export lean_metavar_ctx_assign_delayed]
def assignDelayed (m : MetavarContext) (mvarId : Name) (lctx : LocalContext) (fvars : List Expr) (val : Expr) : MetavarContext :=
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

end MetavarContext
end Lean

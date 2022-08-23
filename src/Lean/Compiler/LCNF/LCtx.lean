/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.LocalContext
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

/--
LCNF local context.
-/
structure LCtx where
  localDecls : Std.HashMap FVarId LocalDecl := {}
  funDecls : Std.HashMap FVarId FunDecl := {}
  fvarIds : Array FVarId := #[]
  deriving Inhabited

def LCtx.addLocalDecl (lctx : LCtx) (fvarId : FVarId) (binderName : Name) (type : Expr) : LCtx :=
  { lctx with
    localDecls := lctx.localDecls.insert fvarId (.cdecl 0 fvarId binderName type .default)
    fvarIds    := lctx.fvarIds.push fvarId }

def LCtx.addLetDecl (lctx : LCtx) (fvarId : FVarId) (binderName : Name) (type : Expr) (value : Expr) : LCtx :=
  { lctx with
    localDecls := lctx.localDecls.insert fvarId (.ldecl 0 fvarId binderName type value true)
    fvarIds    := lctx.fvarIds.push fvarId }

def LCtx.addFunDecl (lctx : LCtx) (funDecl : FunDecl) : LCtx :=
  { lctx with
    localDecls := lctx.localDecls.insert funDecl.fvarId (.cdecl 0 funDecl.fvarId funDecl.binderName funDecl.type .default)
    funDecls   := lctx.funDecls.insert funDecl.fvarId funDecl
    fvarIds    := lctx.fvarIds.push funDecl.fvarId }

/--
Convert a LCNF local context into a regular Lean local context.
-/
def LCtx.toLocalContext (lctx : LCtx) : LocalContext := Id.run do
  let mut result := {}
  for fvarId in lctx.fvarIds do
    let localDecl := lctx.localDecls.find? fvarId |>.get!
    result := result.addDecl localDecl
  return result

end Lean.Compiler.LCNF
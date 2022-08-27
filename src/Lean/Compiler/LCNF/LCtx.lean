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
  deriving Inhabited

def LCtx.addLocalDecl (lctx : LCtx) (fvarId : FVarId) (binderName : Name) (type : Expr) : LCtx :=
  { lctx with
    localDecls := lctx.localDecls.insert fvarId (.cdecl 0 fvarId binderName type .default) }

def LCtx.addLetDecl (lctx : LCtx) (fvarId : FVarId) (binderName : Name) (type : Expr) (value : Expr) : LCtx :=
  { lctx with
    localDecls := lctx.localDecls.insert fvarId (.ldecl 0 fvarId binderName type value true) }

def LCtx.addFunDecl (lctx : LCtx) (funDecl : FunDecl) : LCtx :=
  { lctx with
    localDecls := lctx.localDecls.insert funDecl.fvarId (.cdecl 0 funDecl.fvarId funDecl.binderName funDecl.type .default)
    funDecls   := lctx.funDecls.insert funDecl.fvarId funDecl }

def LCtx.eraseLocal (fvarId : FVarId) : LCtx → LCtx
  | { localDecls, funDecls } =>
    let localDecls := localDecls.erase fvarId
    { localDecls, funDecls }

partial def LCtx.erase (fvarId : FVarId) : LCtx → LCtx
  | { localDecls, funDecls } =>
    let localDecls := localDecls.erase fvarId
    match funDecls.find? fvarId with
    | none => { localDecls, funDecls }
    | some funDecl =>
      let funDecls := funDecls.erase fvarId
      go funDecl.value { localDecls, funDecls }
where
  go (code : Code) (lctx : LCtx) : LCtx :=
    match code with
    | .let decl k => go k <| lctx.eraseLocal decl.fvarId
    | .jp decl k | .fun decl k => go k <| lctx.erase decl.fvarId
    | _ => lctx

/--
Convert a LCNF local context into a regular Lean local context.
-/
def LCtx.toLocalContext (lctx : LCtx) : LocalContext := Id.run do
  let mut result := {}
  for (_, localDecl) in lctx.localDecls.toArray do
    result := result.addDecl localDecl
  return result

end Lean.Compiler.LCNF
/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.LocalContext
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

/--
LCNF local context.
-/
structure LCtx where
  params   : Std.HashMap FVarId Param := {}
  letDecls : Std.HashMap FVarId LetDecl := {}
  funDecls : Std.HashMap FVarId FunDecl := {}
  deriving Inhabited

def LCtx.addParam (lctx : LCtx) (param : Param) : LCtx :=
  { lctx with params := lctx.params.insert param.fvarId param }

def LCtx.addLetDecl (lctx : LCtx) (letDecl : LetDecl) : LCtx :=
  { lctx with letDecls := lctx.letDecls.insert letDecl.fvarId letDecl }

def LCtx.addFunDecl (lctx : LCtx) (funDecl : FunDecl) : LCtx :=
  { lctx with funDecls := lctx.funDecls.insert funDecl.fvarId funDecl }

def LCtx.eraseParam (lctx : LCtx) (param : Param) : LCtx :=
  { lctx with params := lctx.params.erase param.fvarId }

def LCtx.eraseParams (lctx : LCtx) (ps : Array Param) : LCtx :=
  { lctx with params := ps.foldl (init := lctx.params) fun params p => params.erase p.fvarId }

def LCtx.eraseLetDecl (lctx : LCtx) (decl : LetDecl) : LCtx :=
  { lctx with letDecls := lctx.letDecls.erase decl.fvarId }

mutual
  partial def LCtx.eraseFunDecl (lctx : LCtx) (decl : FunDecl) (recursive := true) : LCtx :=
    let lctx := { lctx with funDecls := lctx.funDecls.erase decl.fvarId }
    if recursive then
      eraseCode decl.value <| eraseParams lctx decl.params
    else
      lctx

  partial def LCtx.eraseAlts (alts : Array Alt) (lctx : LCtx) : LCtx :=
    alts.foldl (init := lctx) fun lctx alt =>
      match alt with
      | .default k => eraseCode k lctx
      | .alt _ ps k => eraseCode k <| eraseParams lctx ps

  partial def LCtx.eraseCode (code : Code) (lctx : LCtx) : LCtx :=
    match code with
    | .let decl k => eraseCode k <| lctx.eraseLetDecl decl
    | .jp decl k | .fun decl k => eraseCode k <| eraseFunDecl lctx decl
    | .cases c => eraseAlts c.alts lctx
    | _ => lctx
end

/--
Convert a LCNF local context into a regular Lean local context.
-/
def LCtx.toLocalContext (lctx : LCtx) : LocalContext := Id.run do
  let mut result := {}
  for (_, param) in lctx.params.toArray do
    result := result.addDecl (.cdecl 0 param.fvarId param.binderName param.type .default .default)
  for (_, decl) in lctx.letDecls.toArray do
    result := result.addDecl (.ldecl 0 decl.fvarId decl.binderName decl.type decl.value.toExpr true .default)
  for (_, decl) in lctx.funDecls.toArray do
    result := result.addDecl (.cdecl 0 decl.fvarId decl.binderName decl.type .default .default)
  return result

end Lean.Compiler.LCNF

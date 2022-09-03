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

partial def LCtx.erase (fvarId : FVarId) (lctx : LCtx) (recursive := true) : LCtx :=
  match lctx with
  | { localDecls, funDecls } =>
    let localDecls := localDecls.erase fvarId
    match funDecls.find? fvarId with
    | none => { localDecls, funDecls }
    | some funDecl =>
      let funDecls := funDecls.erase fvarId
      if recursive then
        go funDecl.value <| goParams funDecl.params { localDecls, funDecls }
      else
        { localDecls, funDecls }
where
  goParams (params : Array Param) (lctx : LCtx) : LCtx :=
    params.foldl (init := lctx) fun lctx p => lctx.erase p.fvarId

  goAlts (alts : Array Alt) (lctx : LCtx) : LCtx :=
    alts.foldl (init := lctx) fun lctx alt =>
      match alt with
      | .default k => go k lctx
      | .alt _ ps k => go k <| goParams ps lctx

  go (code : Code) (lctx : LCtx) : LCtx :=
    match code with
    | .let decl k => go k <| lctx.eraseLocal decl.fvarId
    | .jp decl k | .fun decl k => go k <| lctx.erase decl.fvarId
    | .cases c => goAlts c.alts lctx
    | _ => lctx

def LCtx.eraseFVarsAt (c : Code) (lctx : LCtx) : LCtx :=
  LCtx.erase.go c lctx

/--
Convert a LCNF local context into a regular Lean local context.
-/
def LCtx.toLocalContext (lctx : LCtx) : LocalContext := Id.run do
  let mut result := {}
  for (_, localDecl) in lctx.localDecls.toArray do
    result := result.addDecl localDecl
  return result

end Lean.Compiler.LCNF
/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Basic

public section

namespace Lean.Compiler.LCNF

/--
LCNF local context.
-/
structure LCtx where
  paramsPure     : Std.HashMap FVarId (Param .pure) := {}
  paramsImpure   : Std.HashMap FVarId (Param .impure) := {}
  letDeclsPure   : Std.HashMap FVarId (LetDecl .pure) := {}
  letDeclsImpure : Std.HashMap FVarId (LetDecl .impure) := {}
  funDeclsPure   : Std.HashMap FVarId (FunDecl .pure) := {}
  funDeclsImpure : Std.HashMap FVarId (FunDecl .impure) := {}
  deriving Inhabited

def LCtx.addParam (lctx : LCtx) (param : Param pu) : LCtx :=
  match pu with
  | .pure => { lctx with paramsPure := lctx.paramsPure.insert param.fvarId param }
  | .impure => { lctx with paramsImpure := lctx.paramsImpure.insert param.fvarId param }

def LCtx.addLetDecl (lctx : LCtx) (letDecl : LetDecl pu) : LCtx :=
  match pu with
  | .pure => { lctx with letDeclsPure := lctx.letDeclsPure.insert letDecl.fvarId letDecl }
  | .impure => { lctx with letDeclsImpure := lctx.letDeclsImpure.insert letDecl.fvarId letDecl }

def LCtx.addFunDecl (lctx : LCtx) (funDecl : FunDecl pu) : LCtx :=
  match pu with
  | .pure => { lctx with funDeclsPure := lctx.funDeclsPure.insert funDecl.fvarId funDecl }
  | .impure => { lctx with funDeclsImpure := lctx.funDeclsImpure.insert funDecl.fvarId funDecl }

def LCtx.eraseParam (lctx : LCtx) (param : Param pu) : LCtx :=
  match pu with
  | .pure => { lctx with paramsPure := lctx.paramsPure.erase param.fvarId }
  | .impure => { lctx with paramsImpure := lctx.paramsImpure.erase param.fvarId }

def LCtx.eraseParams (lctx : LCtx) (ps : Array (Param pu)) : LCtx :=
  match pu with
  | .pure => { lctx with paramsPure := ps.foldl (init := lctx.paramsPure) fun params p => params.erase p.fvarId }
  | .impure => { lctx with paramsImpure := ps.foldl (init := lctx.paramsImpure) fun params p => params.erase p.fvarId }

def LCtx.eraseLetDecl (lctx : LCtx) (decl : LetDecl pu) : LCtx :=
  match pu with
  | .pure => { lctx with letDeclsPure := lctx.letDeclsPure.erase decl.fvarId }
  | .impure => { lctx with letDeclsImpure := lctx.letDeclsImpure.erase decl.fvarId }

mutual
  partial def LCtx.eraseFunDecl (lctx : LCtx) (decl : FunDecl pu) (recursive := true) : LCtx :=
    let lctx :=
      match pu with
      | .pure => { lctx with funDeclsPure := lctx.funDeclsPure.erase decl.fvarId }
      | .impure => { lctx with funDeclsImpure := lctx.funDeclsImpure.erase decl.fvarId }
    if recursive then
      eraseCode decl.value <| eraseParams lctx decl.params
    else
      lctx

  partial def LCtx.eraseAlts (alts : Array (Alt pu)) (lctx : LCtx) : LCtx :=
    alts.foldl (init := lctx) fun lctx alt =>
      match alt with
      | .default k => eraseCode k lctx
      | .alt _ ps k _ => eraseCode k <| eraseParams lctx ps
      | .ctorAlt _ k _ => eraseCode k lctx

  partial def LCtx.eraseCode (code : Code pu) (lctx : LCtx) : LCtx :=
    match code with
    | .let decl k => eraseCode k <| lctx.eraseLetDecl decl
    | .jp decl k | .fun decl k _ => eraseCode k <| eraseFunDecl lctx decl
    | .cases c => eraseAlts c.alts lctx
    | .uset (k := k) .. | .sset (k := k) .. | .inc (k := k) .. | .dec (k := k) .. =>
      eraseCode k lctx
    | .return .. | .jmp .. | .unreach .. => lctx
end

@[inline]
def LCtx.params (lctx : LCtx) (pu : Purity) : Std.HashMap FVarId (Param pu) :=
  match pu with
  | .pure => lctx.paramsPure
  | .impure => lctx.paramsImpure

@[inline]
def LCtx.letDecls (lctx : LCtx) (pu : Purity) : Std.HashMap FVarId (LetDecl pu) :=
  match pu with
  | .pure => lctx.letDeclsPure
  | .impure => lctx.letDeclsImpure

@[inline]
def LCtx.funDecls (lctx : LCtx) (pu : Purity) : Std.HashMap FVarId (FunDecl pu) :=
  match pu with
  | .pure => lctx.funDeclsPure
  | .impure => lctx.funDeclsImpure

/--
Convert a LCNF local context into a regular Lean local context.
-/
def LCtx.toLocalContext (lctx : LCtx) (pu : Purity) : LocalContext := Id.run do
  let mut result := {}
  for (_, param) in lctx.params pu do
    result := result.addDecl (.cdecl 0 param.fvarId param.binderName param.type .default .default)
  for (_, decl) in lctx.letDecls pu do
    result := result.addDecl (.ldecl 0 decl.fvarId decl.binderName decl.type decl.value.toExpr true .default)
  for (_, decl) in lctx.funDecls pu do
    result := result.addDecl (.cdecl 0 decl.fvarId decl.binderName decl.type .default .default)
  return result

end Lean.Compiler.LCNF

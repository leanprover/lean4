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

def LCtx.addParam (lctx : LCtx) (param : Param ph) : LCtx :=
  match ph with
  | .pure => { lctx with paramsPure := lctx.paramsPure.insert param.fvarId param }
  | .impure => { lctx with paramsImpure := lctx.paramsImpure.insert param.fvarId param }

def LCtx.addLetDecl (lctx : LCtx) (letDecl : LetDecl ph) : LCtx :=
  match ph with
  | .pure => { lctx with letDeclsPure := lctx.letDeclsPure.insert letDecl.fvarId letDecl }
  | .impure => { lctx with letDeclsImpure := lctx.letDeclsImpure.insert letDecl.fvarId letDecl }

def LCtx.addFunDecl (lctx : LCtx) (funDecl : FunDecl ph) : LCtx :=
  match ph with
  | .pure => { lctx with funDeclsPure := lctx.funDeclsPure.insert funDecl.fvarId funDecl }
  | .impure => { lctx with funDeclsImpure := lctx.funDeclsImpure.insert funDecl.fvarId funDecl }

def LCtx.eraseParam (lctx : LCtx) (param : Param ph) : LCtx :=
  match ph with
  | .pure => { lctx with paramsPure := lctx.paramsPure.erase param.fvarId }
  | .impure => { lctx with paramsImpure := lctx.paramsImpure.erase param.fvarId }

def LCtx.eraseParams (lctx : LCtx) (ps : Array (Param ph)) : LCtx :=
  match ph with
  | .pure => { lctx with paramsPure := ps.foldl (init := lctx.paramsPure) fun params p => params.erase p.fvarId }
  | .impure => { lctx with paramsImpure := ps.foldl (init := lctx.paramsImpure) fun params p => params.erase p.fvarId }

def LCtx.eraseLetDecl (lctx : LCtx) (decl : LetDecl ph) : LCtx :=
  match ph with
  | .pure => { lctx with letDeclsPure := lctx.letDeclsPure.erase decl.fvarId }
  | .impure => { lctx with letDeclsImpure := lctx.letDeclsImpure.erase decl.fvarId }

mutual
  partial def LCtx.eraseFunDecl (lctx : LCtx) (decl : FunDecl ph) (recursive := true) : LCtx :=
    let lctx :=
      match ph with
      | .pure => { lctx with funDeclsPure := lctx.funDeclsPure.erase decl.fvarId }
      | .impure => { lctx with funDeclsImpure := lctx.funDeclsImpure.erase decl.fvarId }
    if recursive then
      eraseCode decl.value <| eraseParams lctx decl.params
    else
      lctx

  partial def LCtx.eraseAlts (alts : Array (Alt ph)) (lctx : LCtx) : LCtx :=
    alts.foldl (init := lctx) fun lctx alt =>
      match alt with
      | .default k => eraseCode k lctx
      | .alt _ ps k _ => eraseCode k <| eraseParams lctx ps

  partial def LCtx.eraseCode (code : Code ph) (lctx : LCtx) : LCtx :=
    match code with
    | .let decl k => eraseCode k <| lctx.eraseLetDecl decl
    | .jp decl k | .fun decl k _ => eraseCode k <| eraseFunDecl lctx decl
    | .cases c => eraseAlts c.alts lctx
    | _ => lctx
end

@[inline]
def LCtx.params (lctx : LCtx) (ph : IRPhase) : Std.HashMap FVarId (Param ph) :=
  match ph with
  | .pure => lctx.paramsPure
  | .impure => lctx.paramsImpure

@[inline]
def LCtx.letDecls (lctx : LCtx) (ph : IRPhase) : Std.HashMap FVarId (LetDecl ph) :=
  match ph with
  | .pure => lctx.letDeclsPure
  | .impure => lctx.letDeclsImpure

@[inline]
def LCtx.funDecls (lctx : LCtx) (ph : IRPhase) : Std.HashMap FVarId (FunDecl ph) :=
  match ph with
  | .pure => lctx.funDeclsPure
  | .impure => lctx.funDeclsImpure

/--
Convert a LCNF local context into a regular Lean local context.
-/
def LCtx.toLocalContext (lctx : LCtx) (ph : IRPhase) : LocalContext := Id.run do
  let mut result := {}
  for (_, param) in lctx.params ph do
    result := result.addDecl (.cdecl 0 param.fvarId param.binderName param.type .default .default)
  for (_, decl) in lctx.letDecls ph do
    result := result.addDecl (.ldecl 0 decl.fvarId decl.binderName decl.type decl.value.toExpr true .default)
  for (_, decl) in lctx.funDecls ph do
    result := result.addDecl (.cdecl 0 decl.fvarId decl.binderName decl.type .default .default)
  return result

end Lean.Compiler.LCNF

/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.PrettyPrinter
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF

private abbrev indentD := Std.Format.indentD

namespace PP

abbrev M := ReaderT LocalContext CompilerM

private def join (as : Array α) (f : α → M Format) : M Format := do
  if h : 0 < as.size then
    let mut result ← f as[0]
    for a in as[1:] do
      result := f!"{result} {← f a}"
    return result
  else
    return .nil

private def prefixJoin (pre : Format) (as : Array α) (f : α → M Format) : M Format := do
  let mut result := .nil
  for a in as do
    result := f!"{result}{pre}{← f a}"
  return result

def ppFVar (fvarId : FVarId) : M Format := do
  let localDecl ← getLocalDecl fvarId
  return format localDecl.userName

def ppExpr (e : Expr) : M Format := do
  Meta.ppExpr e |>.run' { lctx := (← read) }

def ppArg (e : Expr) : M Format := do
  if e.isFVar then
    ppFVar e.fvarId!
  else if pp.explicit.get (← getOptions) then
    ppExpr e
  else
    return "_"

def ppArgs (args : Array Expr) : M Format := do
  join args ppArg

def ppApp (e : Expr) : M Format := do
  return f!"{← ppExpr e.getAppFn} {← ppArgs e.getAppArgs}"

def ppValue (e : Expr) : M Format := do
  match e with
  | .app .. => ppApp e
  | .fvar fvarId => ppFVar fvarId
  | .proj _ i e => return f!"{← ppArg e} # {i}"
  | _ => ppExpr e

def ppParam (param : Param) : M Format := do
  if pp.funBinderTypes.get (← getOptions) then
    return Format.paren f!"{param.binderName} : {← ppExpr param.type}"
  else
    return format param.binderName

def ppParams (params : Array Param) : M Format := do
  prefixJoin " " params ppParam

def ppLetDecl (letDecl : LetDecl) : M Format := do
  if pp.letVarTypes.get (← getOptions) then
    return f!"let {letDecl.binderName} : {← ppExpr letDecl.type} := {← ppValue letDecl.value}"
  else
    return f!"let {letDecl.binderName} := {← ppValue letDecl.value}"

mutual
  partial def ppFunDecl (funDecl : FunDecl) : M Format := do
    return f!"{funDecl.binderName}{← ppParams funDecl.params} :={indentD (← ppCode funDecl.value)}"

  partial def ppAlt (alt : Alt) : M Format := do
    match alt with
    | .default k => return f!"| _ =>{indentD (← ppCode k)}"
    | .alt ctorName params k => return f!"| {ctorName}{← ppParams params} =>{indentD (← ppCode k)}"

  partial def ppCode (c : Code) : M Format := do
    match c with
    | .let decl k => return (← ppLetDecl decl) ++ .line ++ (← ppCode k)
    | .fun decl k => return f!"fun " ++ (← ppFunDecl decl) ++ .line ++ (← ppCode k)
    | .jp decl k => return f!"jp " ++ (← ppFunDecl decl) ++ .line ++ (← ppCode k)
    | .cases c => return f!"cases {← ppFVar c.discr}{← prefixJoin .line c.alts ppAlt}"
    | .return fvarId => ppFVar fvarId
    | .jmp fvarId args => return f!"goto {← ppFVar fvarId} {← ppArgs args}"
    | .unreach .. => return "⊥"
end

def run (x : M α) : CompilerM α :=
  withOptions (pp.sanitizeNames.set · false) do
    x |>.run (← get).lctx.toLocalContext

end PP

def ppCode (code : Code) : CompilerM Format :=
  PP.run <| PP.ppCode code

def ppDecl (decl : Decl) : CompilerM Format :=
  PP.run do
    return f!"def {decl.name}{← PP.ppParams decl.params} :={indentD (← PP.ppCode decl.value)}"

end Lean.Compiler.LCNF

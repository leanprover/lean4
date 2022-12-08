/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.PrettyPrinter
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.Internalize

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

def ppFVar (fvarId : FVarId) : M Format :=
  try
    return format (← getBinderName fvarId)
  catch _ =>
    return format fvarId.name

def ppExpr (e : Expr) : M Format := do
  Meta.ppExpr e |>.run' { lctx := (← read) }

def ppArg (e : Arg) : M Format := do
  match e with
  | .erased => return "◾"
  | .fvar fvarId => ppFVar fvarId
  | .type e =>
    if pp.explicit.get (← getOptions) then
      if e.isConst || e.isProp || e.isType0 || e.isFVar then
        ppExpr e
      else
        return Format.paren (←  ppExpr e)
    else
      return "_"

def ppArgs (args : Array Arg) : M Format := do
  prefixJoin " " args ppArg

def ppLetValue (e : LetValue) : M Format := do
  match e with
  | .erased => return "◾"
  | .value v => ppExpr v.toExpr
  | .proj _ i fvarId => return f!"{← ppFVar fvarId} # {i}"
  | .fvar fvarId args => return f!"{← ppFVar fvarId}{← ppArgs args}"
  | .const declName us args => return f!"{← ppExpr (.const declName us)}{← ppArgs args}"

def ppParam (param : Param) : M Format := do
  let borrow := if param.borrow then "@&" else ""
  if pp.funBinderTypes.get (← getOptions) then
    return Format.paren f!"{param.binderName} : {borrow}{← ppExpr param.type}"
  else
    return format s!"{borrow}{param.binderName}"

def ppParams (params : Array Param) : M Format := do
  prefixJoin " " params ppParam

def ppLetDecl (letDecl : LetDecl) : M Format := do
  if pp.letVarTypes.get (← getOptions) then
    return f!"let {letDecl.binderName} : {← ppExpr letDecl.type} := {← ppLetValue letDecl.value}"
  else
    return f!"let {letDecl.binderName} := {← ppLetValue letDecl.value}"

def getFunType (ps : Array Param) (type : Expr) : CoreM Expr :=
  instantiateForall type (ps.map (mkFVar ·.fvarId))

mutual
  partial def ppFunDecl (funDecl : FunDecl) : M Format := do
    return f!"{funDecl.binderName}{← ppParams funDecl.params} : {← ppExpr (← getFunType funDecl.params funDecl.type)} :={indentD (← ppCode funDecl.value)}"

  partial def ppAlt (alt : Alt) : M Format := do
    match alt with
    | .default k => return f!"| _ =>{indentD (← ppCode k)}"
    | .alt ctorName params k => return f!"| {ctorName}{← ppParams params} =>{indentD (← ppCode k)}"

  partial def ppCode (c : Code) : M Format := do
    match c with
    | .let decl k => return (← ppLetDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .fun decl k => return f!"fun " ++ (← ppFunDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .jp decl k => return f!"jp " ++ (← ppFunDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .cases c => return f!"cases {← ppFVar c.discr} : {← ppExpr c.resultType}{← prefixJoin .line c.alts ppAlt}"
    | .return fvarId => return f!"return {← ppFVar fvarId}"
    | .jmp fvarId args => return f!"goto {← ppFVar fvarId}{← ppArgs args}"
    | .unreach type =>
      if pp.all.get (← getOptions) then
        return f!"⊥ : {← ppExpr type}"
      else
        return "⊥"
end

def run (x : M α) : CompilerM α :=
  withOptions (pp.sanitizeNames.set · false) do
    x |>.run (← get).lctx.toLocalContext

end PP

def ppCode (code : Code) : CompilerM Format :=
  PP.run <| PP.ppCode code

def ppLetValue (e : LetValue) : CompilerM Format :=
  PP.run <| PP.ppLetValue e

def ppDecl (decl : Decl) : CompilerM Format :=
  PP.run do
    return f!"def {decl.name}{← PP.ppParams decl.params} : {← PP.ppExpr (← PP.getFunType decl.params decl.type)} :={indentD (← PP.ppCode decl.value)}"

def ppFunDecl (decl : FunDecl) : CompilerM Format :=
  PP.run do
    return f!"fun {← PP.ppFunDecl decl}"

/--
Execute `x` in `CoreM` without modifying `Core`s state.
This is useful if we want make sure we do not affect the next free variable id.
-/
def runCompilerWithoutModifyingState (x : CompilerM α) : CoreM α := do
  let s ← get
  try
    x |>.run {}
  finally
    set s

/--
Similar to `ppDecl`, but in `CoreM`, and it does not assume
`decl` has already been internalized.
This function is used for debugging purposes.
-/
def ppDecl' (decl : Decl) : CoreM Format := do
  runCompilerWithoutModifyingState do
    ppDecl (← decl.internalize)

/--
Similar to `ppCode`, but in `CoreM`, and it does not assume
`code` has already been internalized.
-/
def ppCode' (code : Code) : CoreM Format := do
  runCompilerWithoutModifyingState do
    ppCode (← code.internalize)

end Lean.Compiler.LCNF

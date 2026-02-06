/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.PrettyPrinter.Delaborator.Options
public import Lean.Compiler.LCNF.Internalize
import Init.Data.Format.Macro

public section

namespace Lean.Compiler.LCNF

private abbrev indentD := Std.Format.indentD

namespace PP

abbrev M := ReaderT LocalContext CompilerM

private def join (as : Array α) (f : α → M Format) : M Format := do
  if h : 0 < as.size then
    let mut result ← f as[0]
    for a in as[1...*] do
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

def ppArg (e : Arg pu) : M Format := do
  match e with
  | .erased => return "◾"
  | .fvar fvarId => ppFVar fvarId
  | .type e _ =>
    if pp.explicit.get (← getOptions) then
      if e.isConst || e.isProp || e.isType0 || e.isFVar then
        ppExpr e
      else
        return Format.paren (←  ppExpr e)
    else
      return "_"

def ppArgs (args : Array (Arg pu)) : M Format := do
  prefixJoin " " args ppArg

def ppLitValue (lit : LitValue) : M Format := do
  match lit with
  | .nat v | .uint8 v | .uint16 v | .uint32 v | .uint64 v | .usize v => return format v
  | .str v => return format (repr v)

private def formatCtorInfo : CtorInfo → Format
  | { name := name, cidx := cidx, usize := usize, ssize := ssize, .. } => Id.run do
    let mut r := f!"ctor_{cidx}"
    if usize > 0 || ssize > 0 then
      r := f!"{r}.{usize}.{ssize}"
    if name != Name.anonymous then
      r := f!"{r}[{name}]"
    r

instance : ToFormat CtorInfo := ⟨private_decl% formatCtorInfo⟩

def ppLetValue (e : LetValue pu) : M Format := do
  match e with
  | .erased => return "◾"
  | .lit v => ppLitValue v
  | .proj _ i fvarId _ => return f!"{← ppFVar fvarId} # {i}"
  | .fvar fvarId args => return f!"{← ppFVar fvarId}{← ppArgs args}"
  | .const declName us args _ => return f!"{← ppExpr (.const declName us)}{← ppArgs args}"
  | .ctor i args _ => return f!"{i} {← ppArgs args}"
  | .fap declName args _ => return f!"{declName}{← ppArgs args}"
  | .pap declName args _ => return f!"pap {declName}{← ppArgs args}"
  | .oproj i fvarId _ => return f!"proj[{i}] {← ppFVar fvarId}"
  | .uproj i fvarId _ => return f!"uproj[{i}] {← ppFVar fvarId}"
  | .sproj i offset fvarId _ => return f!"sproj[{i}, {offset}] {← ppFVar fvarId}"
  | .reset n fvarId _ => return f!"reset[{n}] {← ppFVar fvarId}"
  | .reuse fvarId info updateHeader args _ =>
    return f!"reuse" ++ (if updateHeader then f!"!" else f!"") ++ f!" {← ppFVar fvarId} in {info}{← ppArgs args}"

def ppParam (param : Param pu) : M Format := do
  let borrow := if param.borrow then "@&" else ""
  if pp.funBinderTypes.get (← getOptions) then
    return Format.paren f!"{param.binderName} : {borrow}{← ppExpr param.type}"
  else
    return format s!"{borrow}{param.binderName}"

def ppParams (params : Array (Param pu)) : M Format := do
  prefixJoin " " params ppParam

def ppLetDecl (letDecl : LetDecl pu) : M Format := do
  if pp.letVarTypes.get (← getOptions) then
    return f!"let {letDecl.binderName} : {← ppExpr letDecl.type} := {← ppLetValue letDecl.value}"
  else
    return f!"let {letDecl.binderName} := {← ppLetValue letDecl.value}"

def getFunType (ps : Array (Param pu)) (type : Expr) : CoreM Expr :=
  if type.isErased then
    pure type
  else
    match pu with
    | .pure => instantiateForall type (ps.map (mkFVar ·.fvarId))
    | .impure => return type

mutual
  partial def ppFunDecl (funDecl : FunDecl pu) : M Format := do
    return f!"{funDecl.binderName}{← ppParams funDecl.params} : {← ppExpr (← getFunType funDecl.params funDecl.type)} :={indentD (← ppCode funDecl.value)}"

  partial def ppAlt (alt : Alt pu) : M Format := do
    match alt with
    | .default k => return f!"| _ =>{indentD (← ppCode k)}"
    | .alt ctorName params k _ => return f!"| {ctorName}{← ppParams params} =>{indentD (← ppCode k)}"
    | .ctorAlt info k _ => return f!"| {info.name} =>{indentD (← ppCode k)}"

  partial def ppCode (c : Code pu) : M Format := do
    match c with
    | .let decl k => return (← ppLetDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .fun decl k _ => return f!"fun " ++ (← ppFunDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .jp decl k => return f!"jp " ++ (← ppFunDecl decl) ++ ";" ++ .line ++ (← ppCode k)
    | .cases c => return f!"cases {← ppFVar c.discr} : {← ppExpr c.resultType}{← prefixJoin .line c.alts ppAlt}"
    | .return fvarId => return f!"return {← ppFVar fvarId}"
    | .jmp fvarId args => return f!"goto {← ppFVar fvarId}{← ppArgs args}"
    | .unreach type =>
      if pp.all.get (← getOptions) then
        return f!"⊥ : {← ppExpr type}"
      else
        return "⊥"
    | .sset fvarId i offset y ty k _ =>
      if pp.letVarTypes.get (← getOptions) then
        return f!"sset {← ppFVar fvarId} [{i}, {offset}] : {← ppExpr ty} := {← ppFVar y} " ++ ";" ++ .line ++ (← ppCode k)
      else
        return f!"sset {← ppFVar fvarId} [{i}, {offset}] := {← ppFVar y} " ++ ";" ++ .line ++ (← ppCode k)
    | .uset fvarId i y k _ =>
      return f!"uset {← ppFVar fvarId} [{i}] := {← ppFVar y} " ++ ";" ++ .line ++ (← ppCode k)


  partial def ppDeclValue (b : DeclValue pu) : M Format := do
    match b with
    | .code c => ppCode c
    | .extern .. => return "extern"
end

def run (x : M α) : CompilerM α :=
  withOptions (pp.sanitizeNames.set · false) do
    x |>.run ((← get).lctx.toLocalContext (← getPurity))

end PP

def ppCode (code : Code pu) : CompilerM Format :=
  PP.run <| PP.ppCode code

def ppLetValue (e : LetValue pu) : CompilerM Format :=
  PP.run <| PP.ppLetValue e

def ppDecl (decl : Decl pu) : CompilerM Format :=
  PP.run do
    return f!"def {decl.name}{← PP.ppParams decl.params} : {← PP.ppExpr (← PP.getFunType decl.params decl.type)} :={indentD (← PP.ppDeclValue decl.value)}"

def ppFunDecl (decl : FunDecl pu) : CompilerM Format :=
  PP.run do
    return f!"fun {← PP.ppFunDecl decl}"

/--
Execute `x` in `CoreM` without modifying `Core`s state.
This is useful if we want make sure we do not affect the next free variable id.
-/
def runCompilerWithoutModifyingState (phase : Phase) (x : CompilerM α) : CoreM α := do
  let s ← get
  try
    x |>.run (phase := phase)
  finally
    set s

/--
Similar to `ppDecl`, but in `CoreM`, and it does not assume
`decl` has already been internalized.
This function is used for debugging purposes.
-/
def ppDecl' (decl : Decl pu) (phase : Phase) : CoreM Format := do
  runCompilerWithoutModifyingState phase do
    ppDecl (← decl.internalize)

/--
Similar to `ppCode`, but in `CoreM`, and it does not assume
`code` has already been internalized.
-/
def ppCode' (code : Code pu) (phase : Phase) : CoreM Format := do
  runCompilerWithoutModifyingState phase do
    ppCode (← code.internalize)

end Lean.Compiler.LCNF

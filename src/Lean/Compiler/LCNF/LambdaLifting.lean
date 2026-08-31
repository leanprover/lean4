/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.Closure
public import Lean.Compiler.LCNF.MonadScope
public import Lean.Compiler.LCNF.Level
public import Lean.Compiler.LCNF.AuxDeclCache

public section

namespace Lean.Compiler.LCNF
namespace LambdaLifting

/-- Context for the `LiftM` monad. -/
structure Context where
  /--
  If `liftInstParamOnly` is `true`, then only local functions that take
  local instances as parameters are lambda lifted.
  -/
  liftInstParamOnly : Bool := false
  /-- Suffix for the new auxiliary declarations being created. -/
  suffix : Name
  /--
  Declaration where lambda lifting is being applied.
  We use it to provide the "base name" for auxiliary declarations and the flag `safe`.
  -/
  mainDecl : Decl .pure
  /--
  If true, the lambda-lifted functions inherit the inline attribute from `mainDecl`.
  We use this feature to implement `@[inline] instance ...` and `@[always_inline] instance ...`
  -/
  inheritInlineAttrs := false
  /--
  Only local functions with `size > minSize` are lambda lifted.
  We use this feature to implement `@[inline] instance ...` and `@[always_inline] instance ...`
  -/
  minSize : Nat := 0
  /--
  Allow for eta contraction instead of lifting to a lambda if possible.
  -/
  allowEtaContraction : Bool := true


/-- State for the `LiftM` monad. -/
structure State where
  /--
  New auxiliary declarations
  -/
  decls  : Array (Decl .pure) := #[]
  /--
  Next index for generating auxiliary declaration name.
  -/
  nextIdx := 0

/-- Monad for applying lambda lifting. -/
abbrev LiftM := ReaderT Context (StateRefT State (ScopeT CompilerM))

/--
Return `true` if the given declaration takes a local instance as a parameter.
We lambda lift this kind of local function declaration before specialization.
-/
def hasInstParam (decl : FunDecl .pure) : CompilerM Bool :=
  decl.params.anyM fun param => return (← isArrowClass? param.type).isSome

/--
Return `true` if the given declaration should be lambda lifted.
-/
def shouldLift (decl : FunDecl .pure) : LiftM Bool := do
  let minSize := (← read).minSize
  if decl.value.size < minSize then
    return false
  else if (← read).liftInstParamOnly then
    hasInstParam decl
  else
    return true

partial def mkAuxDeclName : LiftM Name := do
  let nextIdx ← modifyGet fun s => (s.nextIdx, { s with nextIdx := s.nextIdx + 1})
  let nameNew := (← read).mainDecl.name ++ (← read).suffix.appendIndexAfter nextIdx
  if (← getDecl? nameNew).isNone then return nameNew
  mkAuxDeclName

def replaceFunDecl (decl : FunDecl .pure) (value : LetValue .pure) : LiftM (LetDecl .pure) := do
  /- We reuse `decl`s `fvarId` to avoid substitution -/
  let declNew := { fvarId := decl.fvarId, binderName := decl.binderName, type := decl.type, value }
  modifyLCtx fun lctx => lctx.addLetDecl declNew
  eraseFunDecl decl
  return declNew

open Internalize in
/--
Create a new auxiliary declaration. The array `closure` contains all free variables
occurring in `decl`.
-/
def mkAuxDecl (closure : Array (Param .pure)) (decl : FunDecl .pure) : LiftM (LetDecl .pure) := do
  let nameNew ← mkAuxDeclName
  let inlineAttr? ← if (← read).inheritInlineAttrs then pure (← read).mainDecl.inlineAttr? else pure none
  let auxDecl ← go nameNew (← read).mainDecl.safe inlineAttr? |>.run' {}
  let us := auxDecl.levelParams.map mkLevelParam
  let auxDeclName ← match (← cacheAuxDecl auxDecl) with
  | .new =>
    auxDecl.save
    modify fun { decls, .. } => { decls := decls.push auxDecl }
    pure auxDecl.name
  | .alreadyCached declName =>
    auxDecl.erase
    pure declName
  let value := .const auxDeclName us (closure.map (.fvar ·.fvarId))
  replaceFunDecl decl value
where
  go (nameNew : Name) (safe : Bool) (inlineAttr? : Option InlineAttributeKind) : InternalizeM .pure (Decl .pure):= do
    let params := (← closure.mapM internalizeParam) ++ (← decl.params.mapM internalizeParam)
    let code ← internalizeCode decl.value
    let type ← code.inferType
    let type ← mkForallParams params type
    let value := .code code
    let decl := { name := nameNew, levelParams := [], params, type, value, safe, inlineAttr?, recursive := false : Decl .pure }
    return decl.setLevelParams

def etaContractibleDecl? (decl : FunDecl .pure) : LiftM (Option (LetDecl .pure)) := do
  if !(← read).allowEtaContraction then return none
  let .let { fvarId := letVar, value := .const declName us args, .. } (.return retVar) := decl.value
    | return none
  if letVar != retVar then return none
  if args.size != decl.params.size then return none
  if (← getDecl? declName).isNone then return none
  for arg in args, param in decl.params do
    let .fvar argVar := arg | return none
    if argVar != param.fvarId then return none

  let value := .const declName us #[]
  replaceFunDecl decl value

mutual
  partial def visitFunDecl (funDecl : FunDecl .pure) : LiftM (FunDecl .pure) := do
    let value ← withParams funDecl.params <| visitCode funDecl.value
    funDecl.update' funDecl.type value

  partial def visitCode (code : Code .pure) : LiftM (Code .pure) := do
    match code with
    | .let decl k =>
      let k ← withFVar decl.fvarId <| visitCode k
      return code.updateLet! decl k
    | .fun decl k =>
      let decl ← visitFunDecl decl
      if (← shouldLift decl) then
        let declNew ← do
          if let some letDecl ← etaContractibleDecl? decl then
            pure letDecl
          else
            let scope ← getScope
            let (_, params, _) ← Closure.run (inScope := scope.contains) <| Closure.collectFunDecl decl
            mkAuxDecl params decl
        let k ← withFVar declNew.fvarId <| visitCode k
        return .let declNew k
      else
        let k ← withFVar decl.fvarId <| visitCode k
        return code.updateFun! decl k
    | .jp decl k =>
      let decl ← visitFunDecl decl
      let k ← withFVar decl.fvarId <| visitCode k
      return code.updateFun! decl k
    | .cases c =>
      let alts ← c.alts.mapMonoM fun alt =>
        match alt with
        | .default k => return alt.updateCode (← visitCode k)
        | .alt _ ps k => withParams ps do return alt.updateCode (← visitCode k)
      return code.updateAlts! alts
    | .unreach .. | .jmp .. | .return .. => return code
end

def main (decl : Decl .pure) : LiftM (Decl .pure) := do
  let value ← withParams decl.params <| decl.value.mapCodeM visitCode
  return { decl with value }

end LambdaLifting

partial def Decl.lambdaLifting (decl : Decl .pure) (liftInstParamOnly : Bool) (allowEtaContraction : Bool)
    (suffix : Name) (inheritInlineAttrs := false) (minSize := 0) : CompilerM (Array (Decl .pure)) := do
  let ctx := {
    mainDecl := decl,
    liftInstParamOnly,
    suffix,
    inheritInlineAttrs,
    minSize,
    allowEtaContraction
  }
  let (decl, s) ← LambdaLifting.main decl |>.run ctx |>.run {} |>.run {}
  return s.decls.push decl

/--
Eliminate all local function declarations.
-/
def lambdaLifting : Pass where
  phase      := .mono
  phaseOut   := .mono
  name       := `lambdaLifting
  run        := fun decls => do
    decls.foldlM (init := #[]) fun decls decl =>
      return decls ++ (← decl.lambdaLifting false true (suffix := `_lam))

/--
During eager lambda lifting, we inspect declarations that are not inlineable or instances (doing it
everywhere can accidentally introduce mutual recursion which the compiler cannot handle well at the
moment). We then lift local function declarations that take local instances as parameters from
their body to ensure they are specialized.
-/
def eagerLambdaLifting : Pass where
  phase      := .base
  phaseOut   := .base
  name       := `eagerLambdaLifting
  run        := fun decls => do
    decls.foldlM (init := #[]) fun decls decl => do
      if decl.inlineable || (← isInstanceReducible decl.name) then
        return decls.push decl
      else
        return decls ++ (← decl.lambdaLifting (liftInstParamOnly := true) (allowEtaContraction := false) (suffix := `_elam))

builtin_initialize
  registerTraceClass `Compiler.eagerLambdaLifting (inherited := true)
  registerTraceClass `Compiler.lambdaLifting (inherited := true)

end Lean.Compiler.LCNF

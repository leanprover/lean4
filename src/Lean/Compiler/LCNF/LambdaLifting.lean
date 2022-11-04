/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Instances
import Lean.Compiler.InlineAttrs
import Lean.Compiler.LCNF.Closure
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.MonadScope
import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.LCNF.Level
import Lean.Compiler.LCNF.AuxDeclCache

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
  mainDecl : Decl
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


/-- State for the `LiftM` monad. -/
structure State where
  /--
  New auxiliary declarations
  -/
  decls  : Array Decl := #[]
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
def hasInstParam (decl : FunDecl) : CompilerM Bool :=
  decl.params.anyM fun param => return (← isArrowClass? param.type).isSome

/--
Return `true` if the given declaration should be lambda lifted.
-/
def shouldLift (decl : FunDecl) : LiftM Bool := do
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

open Internalize in
/--
Create a new auxiliary declaration. The array `closure` contains all free variables
occurring in `decl`.
-/
def mkAuxDecl (closure : Array Param) (decl : FunDecl) : LiftM LetDecl := do
  let nameNew ← mkAuxDeclName
  let inlineAttr? := if (← read).inheritInlineAttrs then (← read).mainDecl.inlineAttr? else none
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
  /- We reuse `decl`s `fvarId` to avoid substitution -/
  let declNew := { fvarId := decl.fvarId, binderName := decl.binderName, type := decl.type, value }
  modifyLCtx fun lctx => lctx.addLetDecl declNew
  eraseFunDecl decl
  return declNew
where
  go (nameNew : Name) (safe : Bool) (inlineAttr? : Option InlineAttributeKind) : InternalizeM Decl := do
    let params := (← closure.mapM internalizeParam) ++ (← decl.params.mapM internalizeParam)
    let value ← internalizeCode decl.value
    let type ← value.inferType
    let type ← mkForallParams params type
    let decl := { name := nameNew, levelParams := [], params, type, value, safe, inlineAttr?, recursive := false : Decl }
    return decl.setLevelParams

mutual
  partial def visitFunDecl (funDecl : FunDecl) : LiftM FunDecl := do
    let value ← withParams funDecl.params <| visitCode funDecl.value
    funDecl.update' funDecl.type value

  partial def visitCode (code : Code) : LiftM Code := do
    match code with
    | .let decl k =>
      let k ← withFVar decl.fvarId <| visitCode k
      return code.updateLet! decl k
    | .fun decl k =>
      let decl ← visitFunDecl decl
      if (← shouldLift decl) then
        let scope ← getScope
        let (_, params, _) ← Closure.run (inScope := scope.contains) <| Closure.collectFunDecl decl
        let declNew ← mkAuxDecl params decl
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

def main (decl : Decl) : LiftM Decl := do
  let value ← withParams decl.params <| visitCode decl.value
  return { decl with value }

end LambdaLifting

partial def Decl.lambdaLifting (decl : Decl) (liftInstParamOnly : Bool) (suffix : Name) (inheritInlineAttrs := false) (minSize := 0) : CompilerM (Array Decl) := do
  let (decl, s) ← LambdaLifting.main decl |>.run { mainDecl := decl, liftInstParamOnly, suffix, inheritInlineAttrs, minSize } |>.run {} |>.run {}
  return s.decls.push decl

/--
Eliminate all local function declarations.
-/
def lambdaLifting : Pass where
  phase      := .mono
  name       := `lambdaLifting
  run        := fun decls => do
    decls.foldlM (init := #[]) fun decls decl => return decls ++ (← decl.lambdaLifting false (suffix := `_lam))

/--
During eager lambda lifting, we lift
- All local function declarations from instances (motivation: make sure it is cheap to inline them later)
- Local function declarations that take local instances as parameters (motivation: ensure they are specialized)
-/
def eagerLambdaLifting : Pass where
  phase      := .base
  name       := `eagerLambdaLifting
  run        := fun decls => do
    decls.foldlM (init := #[]) fun decls decl => do
      if (← Meta.isInstance decl.name) then
        /-
        Recall that we lambda lift local functions in instances to control code blowup, and make sure they are cheap to inline.
        It is not worth to lift tiny ones. TODO: evaluate whether we should add a compiler option to control the min size.

        Recall that when performing eager lambda lifting in instances, we progatate the `[inline]` annotations to the new auxiliary functions.

        Note: we have tried `if decl.inlineable then return decls.push decl`, but it didn't help in our preliminary experiments.
        -/
        return decls ++ (← decl.lambdaLifting (liftInstParamOnly := false) (suffix := `_elam) (inheritInlineAttrs := true) (minSize := 3))
      else
        return decls ++ (← decl.lambdaLifting (liftInstParamOnly := true) (suffix := `_elam))

builtin_initialize
  registerTraceClass `Compiler.eagerLambdaLifting (inherited := true)
  registerTraceClass `Compiler.lambdaLifting (inherited := true)

end Lean.Compiler.LCNF

/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Closure
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.MonadScope
import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.LCNF.Level

namespace Lean.Compiler.LCNF
namespace LambdaLifting

structure Context where
  liftInstParamOnly : Bool := false
  mainDecl : Decl

structure State where
  decls  : Array Decl := #[]

abbrev LiftM := ReaderT Context (StateRefT State (ScopeT CompilerM))

def hasInstParam (decl : FunDecl) : CompilerM Bool :=
  decl.params.anyM fun param => return (← isArrowClass? param.type).isSome

def shouldLift (decl : FunDecl) : LiftM Bool := do
  if (← read).liftInstParamOnly then
    hasInstParam decl
  else
    return true

open Internalize in
def mkAuxDecl (paramsNew : Array Param) (decl : FunDecl) : LiftM LetDecl := do
  let mainDecl := (← read).mainDecl
  let nextIdx := (← get).decls.size
  let nameNew := mainDecl.name ++ (`_lambda).appendIndexAfter nextIdx
  let auxDecl ← go nameNew mainDecl.safe |>.run' {}
  auxDecl.save
  modify fun { decls, .. } => { decls := decls.push auxDecl }
  let us := auxDecl.levelParams.map mkLevelParam
  let value := mkAppN (.const auxDecl.name us) (paramsNew.map (mkFVar ·.fvarId))
  /- We reuse `decl`s `fvarId` to avoid substitution -/
  let declNew := { fvarId := decl.fvarId, binderName := decl.binderName, type := decl.type, value }
  modifyLCtx fun lctx => lctx.addLetDecl declNew
  eraseFunDecl decl
  return declNew
where
  go (nameNew : Name) (safe : Bool) : InternalizeM Decl := do
    let params := (← paramsNew.mapM internalizeParam) ++ (← decl.params.mapM internalizeParam)
    let value ← internalizeCode decl.value
    let type ← value.inferType
    let type ← mkForallParams params type
    let decl := { name := nameNew, levelParams := [], params, type, value, safe, recursive := false : Decl }
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

partial def Decl.lambdaLifting (decl : Decl) (liftInstParamOnly : Bool) : CompilerM (Array Decl) := do
  let (decl, s) ← LambdaLifting.main decl |>.run { mainDecl := decl, liftInstParamOnly } |>.run {} |>.run {}
  return s.decls.push decl

def lambdaLifting : Pass where
  phase      := .mono
  name       := `lambdaLifting
  run        := fun decls => do
    decls.foldlM (init := #[]) fun decls decl => return decls ++ (← decl.lambdaLifting false)

builtin_initialize
  registerTraceClass `Compiler.lambdaLifting (inherited := true)

end Lean.Compiler.LCNF


/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.Specialize
import Lean.Compiler.LCNF.Simp
import Lean.Compiler.LCNF.SpecInfo

namespace Lean.Compiler.LCNF
namespace Specialize

structure Context where
  scope : FVarIdSet := {}

structure State where
  decls : Array Decl := #[]

abbrev SpecializeM := ReaderT Context $ StateRefT State CompilerM

@[inline] def withParams (ps : Array Param) (x : SpecializeM α) : SpecializeM α :=
  withReader (fun ctx => { ctx with scope := ps.foldl (init := ctx.scope) fun s p => s.insert p.fvarId }) x

@[inline] def withFVar (fvarId : FVarId) (x : SpecializeM α) : SpecializeM α :=
  withReader (fun ctx => { ctx with scope := ctx.scope.insert fvarId }) x

def specializeApp? (letDecl : LetDecl) (_k : Code) : SpecializeM (Option Code) := do
  unless letDecl.value.isApp do return none
  let .const declName _us := letDecl.value.getAppFn | return none
  let some paramsInfo ← getSpecParamInfo? declName | return none
  let some _decl ← getStage1Decl? declName | return none
  trace[Compiler.specialize.candidate] "{letDecl.value}, {paramsInfo}"
  -- TODO
  return none

mutual
  partial def visitFunDecl (funDecl : FunDecl) : SpecializeM FunDecl := do
    let value ← withParams funDecl.params <| visitCode funDecl.value
    funDecl.update' funDecl.type value

  partial def visitCode (code : Code) : SpecializeM Code := do
    match code with
    | .let decl k =>
      if let some k ← specializeApp? decl k then
        visitCode k
      else
        let k ← withFVar decl.fvarId <| visitCode k
        return code.updateLet! decl k
    | .fun decl k | .jp decl k =>
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

def main (decl : Decl) : SpecializeM Decl := do
  if (← isTemplateLike decl) then
    return decl
  else
    let value ← withParams decl.params <| visitCode decl.value
    return { decl with value }

end Specialize

partial def Decl.specialize (decl : Decl) : CompilerM (Array Decl) := do
  let (decl, s) ← Specialize.main decl |>.run {} |>.run {}
  return s.decls.push decl

def specialize : Pass where
  phase := .base
  name  := `specialize
  run   := fun decls => do
    saveSpecParamInfo decls
    decls.foldlM (init := #[]) fun decls decl => return decls ++ (← decl.specialize)

builtin_initialize
  registerTraceClass `Compiler.specialize (inherited := true)
  registerTraceClass `Compiler.specialize.candidate

end Lean.Compiler.LCNF
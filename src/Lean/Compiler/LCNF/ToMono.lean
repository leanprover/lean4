/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

def Param.toMono (param : Param) : CompilerM Param := do
  param.update (← toMonoType param.type)

def _root_.Lean.Expr.toMono (e : Expr) : CompilerM Expr := do
  match e with
  | .fvar .. => if isTypeFormerType (← inferType e) then return erasedExpr else return e
  | .lit .. | .const .. => return e
  | .sort .. => return erasedExpr
  | .mvar .. | .bvar .. | .letE .. => unreachable!
  | .mdata _ b => return e.updateMData! (← b.toMono)
  | .proj _ _ b => return e.updateProj! (← b.toMono)
  | .forallE .. | .lam .. => return erasedExpr
  | .app f a =>
    let a ← if a.isFVar then a.toMono else pure erasedExpr
    return e.updateApp! (← f.toMono) a

def LetDecl.toMono (decl : LetDecl) : CompilerM LetDecl := do
  let type ← toMonoType decl.type
  let value ← decl.value.toMono
  decl.update type value

mutual

partial def FunDeclCore.toMono (decl : FunDecl) : CompilerM FunDecl := do
  -- TODO: constructor Decidable to Bool, Trivial Structure
  -- TODO: eliminate projection for trivial structure
  let type ← toMonoType decl.type
  let params ← decl.params.mapM (·.toMono)
  let value ← decl.value.toMono
  decl.update type params value

partial def AltCore.toMono (alt : Alt) : CompilerM Alt := do
  -- TODO: Decidable to Bool, Trivial Structure
  match alt with
  | .default k => return alt.updateCode (← k.toMono)
  | .alt _ ps k => return alt.updateAlt! (← ps.mapM (·.toMono)) (← k.toMono)

partial def Code.toMono (code : Code) : CompilerM Code := do
  match code with
  | .let decl k => return code.updateLet! (← decl.toMono) (← k.toMono)
  | .fun decl k | .jp decl k => return code.updateFun! (← decl.toMono) (← k.toMono)
  | .unreach type => return .unreach (← toMonoType type)
  | .return .. | .jmp .. => return code
  | .cases c =>
    let type ← toMonoType c.resultType
    let alts ← c.alts.mapM (·.toMono)
    return code.updateCases! type c.discr alts

end

def Decl.toMono (decl : Decl) : CompilerM Decl := do
  let type ← toMonoType decl.type
  let params ← decl.params.mapM (·.toMono)
  let value ← decl.value.toMono
  let decl := { decl with type, params, value, levelParams := [] }
  decl.saveMono
  return decl

def toMono : Pass where
  name     := `toMono
  run      := fun decls => decls.mapM (·.toMono)
  phase    := .base
  phaseOut := .mono

builtin_initialize
  registerTraceClass `Compiler.toMono (inherited := true)

end Lean.Compiler.LCNF
/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF
/--
A mapping from free variable id to binder name.
-/
abbrev Renaming := FVarIdMap Name

def Param.applyRenaming (param : Param) (r : Renaming) : CompilerM Param := do
  if let some binderName := r.find? param.fvarId then
    let param := { param with binderName }
    modifyLCtx fun lctx => lctx.addParam param
    return param
  else
    return param

def LetDecl.applyRenaming (decl : LetDecl) (r : Renaming) : CompilerM LetDecl := do
  if let some binderName := r.find? decl.fvarId then
    let decl := { decl with binderName }
    modifyLCtx fun lctx => lctx.addLetDecl decl
    return decl
  else
    return decl

mutual
partial def FunDeclCore.applyRenaming (decl : FunDecl) (r : Renaming) : CompilerM FunDecl := do
  if let some binderName := r.find? decl.fvarId then
    let decl := { decl with binderName }
    modifyLCtx fun lctx => lctx.addFunDecl decl
    decl.updateValue (← decl.value.applyRenaming r)
  else
    decl.updateValue (← decl.value.applyRenaming r)

partial def Code.applyRenaming (code : Code) (r : Renaming) : CompilerM Code := do
  match code with
  | .let decl k => return code.updateLet! (← decl.applyRenaming r) (← k.applyRenaming r)
  | .fun decl k | .jp decl k => return code.updateFun! (← decl.applyRenaming r) (← k.applyRenaming r)
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt =>
      match alt with
      | .default k => return alt.updateCode (← k.applyRenaming r)
      | .alt _ ps k => return alt.updateAlt! (← ps.mapMonoM (·.applyRenaming r)) (← k.applyRenaming r)
    return code.updateAlts! alts
  | .jmp .. | .unreach .. | .return .. => return code
end

def Decl.applyRenaming (decl : Decl) (r : Renaming) : CompilerM Decl := do
  if r.isEmpty then
    return decl
  else
    let params ← decl.params.mapMonoM (·.applyRenaming r)
    let value ← decl.value.applyRenaming r
    return { decl with params, value }

end Lean.Compiler.LCNF
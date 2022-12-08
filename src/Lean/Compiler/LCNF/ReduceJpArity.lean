/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF
/-!
Join point arity reduction.
-/
namespace ReduceJpArity

abbrev ReduceM := ReaderT (FVarIdMap (Array Bool)) CompilerM

partial def reduce (code : Code) : ReduceM Code := do
  match code with
  | .let decl k => return code.updateLet! decl (← reduce k)
  | .fun decl k =>
    let value ← reduce decl.value
    let decl ← decl.update' decl.type value
    return code.updateFun! decl (← reduce k)
  | .jp decl k =>
    let value ← reduce decl.value
    let mut used := value.collectUsed
    let mut mask := #[]
    let mut paramsNew := #[]
    for param in decl.params.reverse do
      if used.contains param.fvarId then
        used := collectUsedAtExpr used param.type
        mask := mask.push true
        paramsNew := paramsNew.push param
      else
        eraseParam param
        mask := mask.push false
    mask := mask.reverse
    paramsNew := paramsNew.reverse
    if paramsNew.size != decl.params.size then
      let type ← mkForallParams paramsNew (← value.inferType)
      let decl ← decl.update type paramsNew value
      let k ← withReader (·.insert decl.fvarId mask) (reduce k)
      return .jp decl k
    else
      let decl ← decl.update' decl.type value
      return code.updateFun! decl (← reduce k)
  | .cases c =>
    let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← reduce alt.getCode)
    return code.updateAlts! alts
  | .return .. | .unreach .. => return code
  | .jmp fvarId args =>
    if let some mask := (← read).find? fvarId then
      let mut argsNew := #[]
      for keep in mask, arg in args do
        if keep then
          argsNew := argsNew.push arg
      return .jmp fvarId argsNew
    else
      return code

end ReduceJpArity

open ReduceJpArity

/--
Try to reduce arity of join points
-/
def Decl.reduceJpArity (decl : Decl) : CompilerM Decl := do
  let value ← reduce decl.value |>.run {}
  return { decl with value }

def reduceJpArity (phase := Phase.base) : Pass :=
  .mkPerDeclaration `reduceJpArity Decl.reduceJpArity phase

builtin_initialize
  registerTraceClass `Compiler.reduceJpArity (inherited := true)

end Lean.Compiler.LCNF

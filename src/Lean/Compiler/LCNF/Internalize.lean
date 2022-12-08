/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.Bind
import Lean.Compiler.LCNF.CompilerM

namespace Lean.Compiler.LCNF

private def refreshBinderName (binderName : Name) : CompilerM Name := do
  match binderName with
  | .num p _ =>
    let r := .num p (← get).nextIdx
    modify fun s => { s with nextIdx := s.nextIdx + 1 }
    return r
  | _ => return binderName

namespace Internalize

abbrev InternalizeM := StateRefT FVarSubst CompilerM

/--
The `InternalizeM` monad is a translator. It "translates" the free variables
in the input expressions and `Code`, into new fresh free variables in the
local context.
-/
instance : MonadFVarSubst InternalizeM true where
  getSubst := get

instance : MonadFVarSubstState InternalizeM where
  modifySubst := modify

private def mkNewFVarId (fvarId : FVarId) : InternalizeM FVarId := do
  let fvarId' ← Lean.mkFreshFVarId
  addFVarSubst fvarId fvarId'
  return fvarId'

def internalizeParam (p : Param) : InternalizeM Param := do
  let binderName ← refreshBinderName p.binderName
  let type ← normExpr p.type
  let fvarId ← mkNewFVarId p.fvarId
  let p := { p with binderName, fvarId, type }
  modifyLCtx fun lctx => lctx.addParam p
  return p

def internalizeLetDecl (decl : LetDecl) : InternalizeM LetDecl := do
  let binderName ← refreshBinderName decl.binderName
  let type ← normExpr decl.type
  let value ← normLetValue decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := { decl with binderName, fvarId, type, value }
  modifyLCtx fun lctx => lctx.addLetDecl decl
  return decl

mutual

partial def internalizeFunDecl (decl : FunDecl) : InternalizeM FunDecl := do
  let type ← normExpr decl.type
  let binderName ← refreshBinderName decl.binderName
  let params ← decl.params.mapM internalizeParam
  let value ← internalizeCode decl.value
  let fvarId ← mkNewFVarId decl.fvarId
  let decl := { decl with binderName, fvarId, params, type, value }
  modifyLCtx fun lctx => lctx.addFunDecl decl
  return decl

partial def internalizeCode (code : Code) : InternalizeM Code := do
  match code with
  | .let decl k => return .let (← internalizeLetDecl decl) (← internalizeCode k)
  | .fun decl k => return .fun (← internalizeFunDecl decl) (← internalizeCode k)
  | .jp decl k => return .jp (← internalizeFunDecl decl) (← internalizeCode k)
  | .return fvarId => withNormFVarResult (← normFVar fvarId) fun fvarId => return .return fvarId
  | .jmp fvarId args => withNormFVarResult (← normFVar fvarId) fun fvarId => return .jmp fvarId (← args.mapM normArg)
  | .unreach type => return .unreach (← normExpr type)
  | .cases c =>
    withNormFVarResult (← normFVar c.discr) fun discr => do
      let resultType ← normExpr c.resultType
      let internalizeAltCode (k : Code) : InternalizeM Code :=
        internalizeCode k
      let alts ← c.alts.mapM fun
        | .alt ctorName params k => return .alt ctorName (← params.mapM internalizeParam) (← internalizeAltCode k)
        | .default k => return .default (← internalizeAltCode k)
      return .cases { c with discr, alts, resultType }

end

partial def internalizeCodeDecl (decl : CodeDecl) : InternalizeM CodeDecl := do
  match decl with
  | .let decl => return .let (← internalizeLetDecl decl)
  | .fun decl => return .fun (← internalizeFunDecl decl)
  | .jp decl => return .jp (← internalizeFunDecl decl)

end Internalize

/--
Refresh free variables ids in `code`, and store their declarations in the local context.
-/
partial def Code.internalize (code : Code) (s : FVarSubst := {}) : CompilerM Code :=
  Internalize.internalizeCode code |>.run' s

open Internalize in
def Decl.internalize (decl : Decl) (s : FVarSubst := {}): CompilerM Decl :=
  go decl |>.run' s
where
  go (decl : Decl) : InternalizeM Decl := do
    let type ← normExpr decl.type
    let params ← decl.params.mapM internalizeParam
    let value ← internalizeCode decl.value
    return { decl with type, params, value }

/--
Create a fresh local context and internalize the given decls.
-/
def cleanup (decl : Array Decl) : CompilerM (Array Decl) := do
  modify fun _ => {}
  decl.mapM fun decl => do
    modify fun s => { s with nextIdx := 1 }
    decl.internalize

def normalizeFVarIds (decl : Decl) : CoreM Decl := do
  let ngenSaved ← getNGen
  setNGen {}
  try
    CompilerM.run <| decl.internalize
  finally
    setNGen ngenSaved

end Lean.Compiler.LCNF

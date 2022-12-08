/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.ToExpr
import Lean.Compiler.LCNF.PassManager

namespace Lean.Compiler.LCNF

/-! Common Sub-expression Elimination -/

namespace CSE

structure State where
  map   : PHashMap Expr FVarId := {}
  subst : FVarSubst := {}

abbrev M := StateRefT State CompilerM

instance : MonadFVarSubst M false where
  getSubst := return (← get).subst

instance : MonadFVarSubstState M where
  modifySubst f := modify fun s => { s with subst := f s.subst }

@[inline] def getSubst : M FVarSubst :=
  return (← get).subst

@[inline] def addEntry (value : Expr) (fvarId : FVarId) : M Unit :=
  modify fun s => { s with map := s.map.insert value fvarId }

@[inline] def withNewScope (x : M α) : M α := do
  let map := (← get).map
  try x finally modify fun s => { s with map }

def replaceLet (decl : LetDecl) (fvarId : FVarId) : M Unit := do
  eraseLetDecl decl
  addFVarSubst decl.fvarId fvarId

def replaceFun (decl : FunDecl) (fvarId : FVarId) : M Unit := do
  eraseFunDecl decl
  addFVarSubst decl.fvarId fvarId

partial def _root_.Lean.Compiler.LCNF.Code.cse (code : Code) : CompilerM Code :=
  go code |>.run' {}
where
  goFunDecl (decl : FunDecl) : M FunDecl := do
    let type ← normExpr decl.type
    let params ← normParams decl.params
    let value ← withNewScope do go decl.value
    decl.update type params value

  go (code : Code) : M Code := do
    match code with
    | .let decl k =>
      let decl ← normLetDecl decl
      -- We only apply CSE to pure code
      let key := decl.value.toExpr
      match (← get).map.find? key with
      | some fvarId =>
        replaceLet decl fvarId
        go k
      | none =>
        addEntry key decl.fvarId
        return code.updateLet! decl (← go k)
    | .fun decl k =>
      let decl ← goFunDecl decl
      let value := decl.toExpr
      match (← get).map.find? value with
      | some fvarId' =>
        replaceFun decl fvarId'
        go k
      | none =>
        addEntry value decl.fvarId
        return code.updateFun! decl (← go k)
    | .jp decl k =>
      let decl ← goFunDecl decl
      /-
       We currently don't eliminate common join points because we want to prevent
       jumps to out-of-scope join points.
      -/
      return code.updateFun! decl (← go k)
    | .cases c =>
      withNormFVarResult (← normFVar c.discr) fun discr => do
        let resultType ← normExpr c.resultType
        let alts ← c.alts.mapMonoM fun alt => do
          match alt with
          | .alt _ ps k => withNewScope do
            return alt.updateAlt! (← normParams ps) (← go k)
          | .default k => withNewScope do return alt.updateCode (← go k)
        return code.updateCases! resultType discr alts
    | .return fvarId => withNormFVarResult (← normFVar fvarId) fun fvarId => return code.updateReturn! fvarId
    | .jmp fvarId args => withNormFVarResult (← normFVar fvarId) fun fvarId => return code.updateJmp! fvarId (← normArgs args)
    | .unreach .. => return code

end CSE

/--
Common sub-expression elimination
-/
def Decl.cse (decl : Decl) : CompilerM Decl := do
  let value ← decl.value.cse
  return { decl with value }

def cse (phase : Phase := .base) (occurrence := 0) : Pass :=
  .mkPerDeclaration `cse Decl.cse phase occurrence

builtin_initialize
  registerTraceClass `Compiler.cse (inherited := true)

end Lean.Compiler.LCNF

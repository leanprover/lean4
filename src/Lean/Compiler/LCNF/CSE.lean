/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Compiler.LCNF.ToExpr
public import Lean.Compiler.LCNF.PassManager
public import Lean.Compiler.NeverExtractAttr

public section

namespace Lean.Compiler.LCNF

/-! Common Sub-expression Elimination -/

namespace CSE

structure State where
  map   : PHashMap Expr FVarId := {}
  subst : FVarSubst .pure := {}

abbrev M := StateRefT State CompilerM

instance : MonadFVarSubst M .pure false where
  getSubst := return (← get).subst

instance : MonadFVarSubstState M .pure where
  modifySubst f := modify fun s => { s with subst := f s.subst }

@[inline] def getSubst : M (FVarSubst .pure) :=
  return (← get).subst

@[inline] def addEntry (value : Expr) (fvarId : FVarId) : M Unit :=
  modify fun s => { s with map := s.map.insert value fvarId }

@[inline] def withNewScope (x : M α) : M α := do
  let map := (← get).map
  try x finally modify fun s => { s with map }

def replaceLet (decl : LetDecl .pure) (fvarId : FVarId) : M Unit := do
  eraseLetDecl decl
  addFVarSubst decl.fvarId fvarId

def replaceFun (decl : FunDecl .pure) (fvarId : FVarId) : M Unit := do
  eraseFunDecl decl
  addFVarSubst decl.fvarId fvarId

def hasNeverExtract (v : LetValue .pure) : CompilerM Bool :=
  match v with
  | .const declName .. =>
    return hasNeverExtractAttribute (← getEnv) declName
  | .lit _ | .erased | .proj .. | .fvar .. =>
    return false

partial def _root_.Lean.Compiler.LCNF.Code.cse (shouldElimFunDecls : Bool) (code : Code .pure) :
    CompilerM (Code .pure) :=
  go code |>.run' {}
where
  goFunDecl (decl : FunDecl .pure) : M (FunDecl .pure) := do
    let type ← normExpr decl.type
    let params ← normParams decl.params
    let value ← withNewScope do go decl.value
    decl.update type params value

  go (code : Code .pure) : M (Code .pure) := do
    match code with
    | .let decl k =>
      let decl ← normLetDecl decl
      if (← hasNeverExtract decl.value) then
        return code.updateLet! decl (← go k)
      else
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
      if shouldElimFunDecls then
        let value := decl.toExpr
        match (← get).map.find? value with
        | some fvarId' =>
          replaceFun decl fvarId'
          go k
        | none =>
          addEntry value decl.fvarId
          return code.updateFun! decl (← go k)
      else
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
def Decl.cse (shouldElimFunDecls : Bool) (decl : Decl .pure) : CompilerM (Decl .pure) := do
  let value ← decl.value.mapCodeM (·.cse shouldElimFunDecls)
  return { decl with value }

def cse (phase : Phase := .base) (shouldElimFunDecls := false) (occurrence := 0) : Pass :=
  phase.withPurityCheck .pure fun h =>
    .mkPerDeclaration `cse phase (h ▸ Decl.cse shouldElimFunDecls) occurrence

builtin_initialize
  registerTraceClass `Compiler.cse (inherited := true)

end Lean.Compiler.LCNF

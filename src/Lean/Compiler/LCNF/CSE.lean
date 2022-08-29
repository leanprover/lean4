/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.ToExpr

namespace Lean.Compiler.LCNF

/-! Common Sub-expression Elimination -/

namespace CSE

structure State where
  map   : Std.PHashMap Expr FVarId := {}
  subst : FVarSubst := {}

abbrev M := StateRefT State CompilerM

@[inline] def getSubst : M FVarSubst :=
  return (← get).subst

@[inline] def addEntry (value : Expr) (fvarId : FVarId) : M Unit :=
  modify fun s => { s with map := s.map.insert value fvarId }

@[inline] def addSubst (fvarId fvarId' : FVarId) : M Unit :=
  modify fun s => { s with subst := s.subst.insert fvarId (.fvar fvarId') }

@[inline] def withNewScope (x : M α) : M α := do
  let map := (← get).map
  try x finally modify fun s => { s with map }

def replaceFVar (fvarId fvarId' : FVarId) : M Unit := do
  eraseFVar fvarId
  addSubst fvarId fvarId'

end CSE

open CSE in
partial def Code.cse (code : Code) : CompilerM Code :=
  go code |>.run' {}
where
  goFunDecl (decl : FunDecl) : M FunDecl := do
    let type := (← getSubst).applyToExpr decl.type
    let params ← (← getSubst).applyToParams decl.params
    let value ← withNewScope do go decl.value
    decl.update type params value

  go (code : Code) : M Code := do
    match code with
    | .let decl k =>
      let decl ← (← getSubst).applyToLetDecl decl
      if decl.pure then
        -- We only apply CSE to pure code
        match (← get).map.find? decl.value with
        | some fvarId' =>
          replaceFVar decl.fvarId fvarId'
          go k
        | none =>
          addEntry decl.value decl.fvarId
          return code.updateLet! decl (← go k)
      else
        return code.updateLet! decl (← go k)
    | .fun decl k =>
      let decl ← goFunDecl decl
      let value := decl.toExpr
      match (← get).map.find? value with
      | some fvarId' =>
        replaceFVar decl.fvarId fvarId'
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
      let discr := (← getSubst).applyToFVar c.discr
      let resultType := (← getSubst).applyToExpr c.resultType
      let alts ← c.alts.mapMonoM fun alt => do
        match alt with
        | .alt _ ps k => withNewScope do
          let ps ← (← getSubst).applyToParams ps
          return alt.updateAlt! ps (← go k)
        | .default k => withNewScope do return alt.updateCode (← go k)
      return code.updateCases! resultType discr alts
    | .return fvarId => return code.updateReturn! ((← getSubst).applyToFVar fvarId)
    | .jmp fvarId args => return code.updateJmp! ((← getSubst).applyToFVar fvarId) (← args.mapMonoM fun arg => return (← getSubst).applyToExpr arg)
    | .unreach .. => return code

/--
Common sub-expression elimination
-/
def Decl.cse (decl : Decl) : CompilerM Decl := do
  let value ← decl.value.cse
  return { decl with value }

end Lean.Compiler.LCNF

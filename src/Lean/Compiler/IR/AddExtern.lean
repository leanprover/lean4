/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/

module

prelude
public import Lean.Compiler.IR.Boxing
import Lean.Compiler.IR.RC
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.LCNF.ToImpure
import Init.While

public section

namespace Lean.IR

@[export lean_add_extern]
def addExtern (declName : Name) (externAttrData : ExternAttrData) : CoreM Unit := do
  if !isPrivateName declName then
    modifyEnv (Compiler.LCNF.setDeclPublic · declName)
  let monoDecl ← addMono declName
  let impureDecl ← addImpure monoDecl
  addIr impureDecl
where
  addMono (declName : Name) : CoreM (Compiler.LCNF.Decl .pure) := do
    let type ← Compiler.LCNF.getOtherDeclMonoType declName
    let mut typeIter := type
    let mut params := #[]
    repeat
      let .forallE binderName ty b _ := typeIter | break
      let borrow := isMarkedBorrowed ty
      params := params.push {
        fvarId := (← mkFreshFVarId)
        type := ty,
        binderName,
        borrow
      }
      typeIter := b
    let decl := {
      name := declName,
      levelParams := [],
      value := .extern externAttrData,
      inlineAttr? := some .noinline,
      type,
      params,
    }
    decl.saveMono
    return decl

  addImpure (decl : Compiler.LCNF.Decl .pure) : CoreM (Compiler.LCNF.Decl .impure) := do
    let type ← Compiler.LCNF.lowerResultType decl.type decl.params.size
    let params ← decl.params.mapM fun param =>
      return { param with type := ← Compiler.LCNF.toImpureType param.type }
    let decl := {
      name := decl.name,
      levelParams := decl.levelParams,
      value := .extern externAttrData
      inlineAttr? := some .noinline,
      type,
      params
    }
    decl.saveImpure
    return decl

  addIr (decl : Compiler.LCNF.Decl .impure) : CoreM Unit := do
    let params := decl.params.mapIdx fun idx param =>
      { x := ⟨idx⟩, borrow := param.borrow, ty := toIRType param.type  }
    let type := toIRType decl.type
    let decls := #[.extern declName params type externAttrData]
    let decls := ExplicitBoxing.addBoxedVersions (← Lean.getEnv) decls
    let decls ← explicitRC decls
    logDecls `result decls
    addDecls decls

end Lean.IR

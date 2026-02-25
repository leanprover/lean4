/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/

module

prelude
import Init.While
import Lean.Compiler.IR.ToIR
import Lean.Compiler.LCNF.ToImpureType
import Lean.Compiler.LCNF.ToImpure
import Lean.Compiler.LCNF.ExplicitBoxing
import Lean.Compiler.LCNF.Internalize
public import Lean.Compiler.ExternAttr
import Lean.Compiler.LCNF.ExplicitRC

public section

namespace Lean.IR

@[export lean_add_extern]
def addExtern (declName : Name) (externAttrData : ExternAttrData) : CoreM Unit := do
  if !isPrivateName declName then
    modifyEnv (Compiler.LCNF.setDeclPublic · declName)
  let monoDecl ← addMono declName
  let impureDecls ← addImpure monoDecl
  addIr impureDecls
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

  addImpure (decl : Compiler.LCNF.Decl .pure) : CoreM (Array (Compiler.LCNF.Decl .impure)) := do
    let type ← Compiler.LCNF.lowerResultType decl.type decl.params.size
    let params ← decl.params.mapM fun param =>
      return { param with type := ← Compiler.LCNF.toImpureType param.type }
    let decl : Compiler.LCNF.Decl .impure := {
      name := decl.name,
      levelParams := decl.levelParams,
      value := .extern externAttrData
      inlineAttr? := some .noinline,
      type,
      params
    }
    Compiler.LCNF.CompilerM.run (phase := .impure) do
      let decl ← decl.internalize
      decl.saveImpure
      let decls ← Compiler.LCNF.addBoxedVersions #[decl]
      let decls ← Compiler.LCNF.runExplicitRc decls
      return decls

  addIr (decls : Array (Compiler.LCNF.Decl .impure)) : CoreM Unit := do
    let decls ← toIR decls
    logDecls `result decls
    addDecls decls

end Lean.IR

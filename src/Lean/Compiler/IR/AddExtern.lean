/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/

module

prelude
public import Lean.Compiler.IR.Boxing

public section

namespace Lean.IR

@[export lean_add_extern]
def addExtern (declName : Name) (externAttrData : ExternAttrData) : CoreM Unit := do
  let mut type ← Compiler.LCNF.getOtherDeclMonoType declName
  let mut params := #[]
  let mut nextVarIndex := 0
  repeat
    let .forallE _ d b _ := type | break
    let borrow := isMarkedBorrowed d
    let ty ← toIRType d
    params := params.push { x := ⟨nextVarIndex⟩, borrow, ty }
    type := b
    nextVarIndex := nextVarIndex + 1
  let irType ← toIRType type
  let decl := .extern declName params irType externAttrData
  addDecl decl
  if !isPrivateName decl.name then
    modifyEnv (Compiler.LCNF.setDeclPublic · decl.name)
  if ExplicitBoxing.requiresBoxedVersion (← Lean.getEnv) decl then
    addDecl (ExplicitBoxing.mkBoxedVersion decl)

end Lean.IR

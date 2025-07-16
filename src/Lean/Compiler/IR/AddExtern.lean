/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Zwarich
-/

prelude
import Lean.CoreM
import Lean.Compiler.BorrowedAnnotation
import Lean.Compiler.ExternAttr
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.Boxing
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.ToIRType
import Lean.Compiler.LCNF.MonoTypes

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
  -- TODO: Remove this code duplication once IR.CompilerM is based on CoreM.
  Lean.modifyEnv fun env => addDeclAux env decl
  if ExplicitBoxing.requiresBoxedVersion (← Lean.getEnv) decl then
    Lean.modifyEnv fun env => addDeclAux env (ExplicitBoxing.mkBoxedVersion decl)

end Lean.IR

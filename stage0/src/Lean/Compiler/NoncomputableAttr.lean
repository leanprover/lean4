/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment

namespace Lean

builtin_initialize noncomputableExt : TagDeclarationExtension ← mkTagDeclarationExtension

/-- Mark in the environment extension that the given declaration has been declared by the user as `noncomputable`. -/
def addNoncomputable (env : Environment) (declName : Name) : Environment :=
  noncomputableExt.tag env declName

/--
  Return true iff the user has declared the given declaration as `noncomputable`.
  Remark: we use this function only for introspection. It is currently not used by the code generator.
-/
def isNoncomputable (env : Environment) (declName : Name) : Bool :=
  noncomputableExt.isTagged env declName

end Lean

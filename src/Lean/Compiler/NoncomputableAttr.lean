/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.EnvExtension

public section

namespace Lean

builtin_initialize noncomputableExt : TagDeclarationExtension ← mkTagDeclarationExtension

/-- Mark in the environment extension that the given declaration has been declared by the user as `noncomputable`. -/
def addNoncomputable (env : Environment) (declName : Name) : Environment :=
  noncomputableExt.tag env declName

/--
Returns `true` when the given declaration is tagged `noncomputable`.
-/
def isNoncomputable (env : Environment) (declName : Name) : Bool :=
  noncomputableExt.isTagged env declName

end Lean

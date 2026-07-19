/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.Theorems
public section
namespace Lean.Meta.Grind

/-- Extension backing the `@[grind homo]` attribute. -/
builtin_initialize homoExt : Sym.Simp.SymSimpExtension ← Sym.Simp.mkSymSimpExt

/-- Returns the homomorphism rules tagged with the `[grind homo]` attribute. -/
def getHomoTheorems : CoreM Sym.Simp.Theorems :=
  homoExt.getTheorems

end Lean.Meta.Grind

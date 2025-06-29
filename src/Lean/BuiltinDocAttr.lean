/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Lean.Compiler.InitAttr
import Lean.DocString.Extension

namespace Lean

def declareBuiltinDocStringAndRanges (declName : Name) : AttrM Unit := do
  if let some doc ← findSimpleDocString? (← getEnv) declName (includeBuiltin := false) then
    declareBuiltin (declName ++ `docString) (mkAppN (mkConst ``addBuiltinDocString) #[toExpr declName, toExpr doc])
  if let some declRanges ← findDeclarationRanges? declName then
    declareBuiltin (declName ++ `declRange) (mkAppN (mkConst ``addBuiltinDeclarationRanges) #[toExpr declName, toExpr declRanges])

/--
Makes the documentation and location of a declaration available as a builtin.

This allows the documentation of core Lean features to be visible without importing the file they
are defined in. This is only useful during bootstrapping and should not be used outside of
the Lean source code.
-/
@[builtin_doc]
builtin_initialize
  registerBuiltinAttribute {
    name  := `builtin_doc
    descr := "make the docs and location of this declaration available as a builtin"
    add   := fun decl stx _ => do
      Attribute.Builtin.ensureNoArgs stx
      declareBuiltinDocStringAndRanges decl
  }

end Lean

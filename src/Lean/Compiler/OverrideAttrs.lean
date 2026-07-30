/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module
prelude
public import Lean.Compiler.InductiveOverride
public import Lean.Compiler.LCNF.Types

public section

namespace Lean.Compiler

open LCNF.ImpureType

builtin_initialize
  registerBuiltinAttribute {
    name := `override_runtime_type
    descr := "override impure type of a declaration"
    add := fun declName stx kind => do
      unless kind == .global do
        throwAttrMustBeGlobal `override_runtime_type kind
      let type := (← Attribute.Builtin.getId? stx).getD `tobject
      let impureType : Expr := .const type []
      unless impureType.isValidImpureType do
        throwErrorAt (← Attribute.Builtin.getIdent stx) "`{type}` is not a valid impure type"
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule `override_runtime_type declName
      if hasInductiveOverride env declName then
        throwError "`{declName}` already has an override, cannot apply another"
      modifyEnv (addInductiveOverride · (.simpleType declName impureType))
    applicationTime := .afterTypeChecking
  }

end Lean.Compiler

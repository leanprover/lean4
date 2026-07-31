/-
Copyright (c) 2026 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module
prelude
import Lean.Compiler.InductiveOverride
import Lean.Compiler.LCNF.Types
import Lean.Compiler.LCNF.ToImpureType

public section

namespace Lean.Compiler

open LCNF ImpureType

builtin_initialize
  registerBuiltinAttribute {
    name := `override_runtime_type
    descr := "override impure type of a declaration"
    add := fun declName stx kind => do
      unless kind == .global do
        throwAttrMustBeGlobal `override_runtime_type kind
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwAttrDeclInImportedModule `override_runtime_type declName
      if hasInductiveOverride env declName then
        throwError "`{declName}` already has an override, cannot apply another"
      if ← didCompileInductive declName then
        throwError "The `[override_runtime_type]` attribute cannot be used after the declaration"
      let type := (← getConstVal declName).type
      unless ← (Meta.isTypeFormerType type).run' do
        throwError "Invalid `[override_runtime_type]` attribute, the declaration isn't a type"
      let typeIdent? ← Attribute.Builtin.getIdent? stx
      let impureType : Expr := .const ((typeIdent?.map (·.getId)).getD `tobj) []
      unless impureType.isValidImpureType do
        throwErrorAt typeIdent?.get! "`{typeIdent?}` is not a valid impure type"
      modifyEnv (addInductiveOverride · (.simpleType declName impureType))
    applicationTime := .afterTypeChecking
  }

end Lean.Compiler

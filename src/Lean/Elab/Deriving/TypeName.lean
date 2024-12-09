/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner
-/
prelude
import Lean.Elab.Deriving.Basic

namespace Lean.Elab
open Command Std Parser Term

private def deriveTypeNameInstance (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    let cinfo ← getConstInfo declName
    unless cinfo.levelParams.isEmpty do
      throwError m!"{.ofConstName declName} has universe level parameters"
    elabCommand <| ← withFreshMacroScope `(
      unsafe def instImpl : TypeName @$(mkCIdent declName) := .mk _ $(quote declName)
      @[implemented_by instImpl] opaque inst : TypeName @$(mkCIdent declName)
      instance : TypeName @$(mkCIdent declName) := inst
    )
  return true

initialize
  registerDerivingHandler ``TypeName deriveTypeNameInstance

/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Elab.Command
import Init.Grind.Lint
import Lean.Meta.Tactic.Grind.EMatchTheorem
import Lean.EnvExtension
import Lean.Elab.Tactic.Grind.Config
namespace Lean.Elab.Tactic.Grind

builtin_initialize skipExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

builtin_initialize muteExt : SimplePersistentEnvExtension Name NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.insert)
    addImportedFn := mkStateFromImportedEntries (·.insert) {}
  }

open Command

private def checkEMatchTheorem (declName : Name) : CoreM Unit := do
  unless (← Meta.Grind.isEMatchTheorem declName) do
    throwError "`{declName}` is not marked with the `@[grind]` attribute for theorem instantiation"

@[builtin_command_elab Lean.Grind.grindLintSkip]
def elabGrindLintSkip : CommandElab := fun stx => do
  let `(#grind_lint skip $ids:ident*) := stx | throwUnsupportedSyntax
  liftTermElabM do
  for id in ids do
    let declName ← realizeGlobalConstNoOverloadWithInfo id
    checkEMatchTheorem declName
    if skipExt.getState (← getEnv) |>.contains declName then
      throwError "`{declName}` is already in the `#grind_lint` skip set"
    modifyEnv fun env => skipExt.addEntry env declName

@[builtin_command_elab Lean.Grind.grindLintMute]
def elabGrindLintMute : CommandElab := fun stx => do
  let `(#grind_lint mute $ids:ident*) := stx | throwUnsupportedSyntax
  liftTermElabM do
  for id in ids do
    let declName ← realizeGlobalConstNoOverloadWithInfo id
    checkEMatchTheorem declName
    if muteExt.getState (← getEnv) |>.contains declName then
      throwError "`{declName}` is already in the `#grind_lint` mute set"
    modifyEnv fun env => muteExt.addEntry env declName

end Lean.Elab.Tactic.Grind

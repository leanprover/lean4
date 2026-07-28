/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Linter.CodeQuality.Basic
public import Lean.Elab.InfoTree.Main

public section

open Lean Meta

namespace Lean.Linter.CodeQuality

/-!
# Code quality check registration and driver

A code quality check is a declaration of type `Check` tagged with the
`@[code_quality_check]` attribute. Registered checks are tracked by the
`checkExt` environment extension and are run concurrently, one task per check,
by `runChecks`, which combines all results into a single `Report`.
-/

structure NamedCheck where
  declName : Name
  run : Check

def getCheck (declName : Name) : CoreM Check := unsafe
  evalConstCheck Check ``Check declName

builtin_initialize checkExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss => nss.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

builtin_initialize registerBuiltinAttribute {
  name := `code_quality_check
  descr := "Use this declaration as a check in the code quality metrics driver"
  add := fun decl _stx kind => do
    unless kind == .global do
      throwError "invalid attribute `code_quality_check`, must be global"
    let env ← getEnv
    let isPublic := !isPrivateName decl; let isMeta := isMarkedMeta env decl
    unless isPublic && isMeta do
      throwError "invalid attribute `code_quality_check`, \
        declaration `{.ofConstName decl}` must be marked as `public` and `meta`\
        {if isPublic then " but is only marked `public`" else ""}\
        {if isMeta then " but is only marked `meta`" else ""}"
    let constInfo ← getConstInfo decl
    unless ← (isDefEq constInfo.type (mkConst ``Check)).run' do
      throwError "`{.ofConstName decl}` must have type `{.ofConstName ``Check}`, got \
        `{constInfo.type}`"
    modifyEnv fun env => checkExt.addEntry env decl
}

def getChecks : CoreM (Array NamedCheck) := do
  (checkExt.getState (← getEnv)).mapM fun declName =>
    return { declName, run := ← getCheck declName }

def runChecks (checks : Array NamedCheck) : BaseIO Report := do
  let tasks ← checks.mapM fun check =>
    (check.declName, ·) <$> IO.asTask (check.run ())
  let mut entries := #[]
  let mut failures := #[]
  for (declName, task) in tasks do
    match task.get with
    | .ok checkEntries => entries := entries ++ checkEntries
    | .error err => failures := failures.push { name := toString declName, message := toString err }
  return { entries, failures }

end Lean.Linter.CodeQuality

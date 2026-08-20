/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Lean.Linter.CodeQuality.Basic
public import Lean.Message
public import Lean.Elab.InfoTree.Main
import Lean.Elab.Command

public section

open Lean Meta

namespace Lean.Linter.CodeQuality

/-!
# Code quality check registration and driver

A package code quality check is a declaration of type `PackageCheck` tagged with the
`@[package_code_quality_check]` attribute. The driver runs every registered check,
providing it with the data encapsulated in `PackageCheckContext`. All checks are
tracked by the `packageCheckExt` environment extension and are run concurrently,
one task per check, by `runPackageChecks`, which combines all results
into a single array of entries and accumulates all errors.
-/

/-- Global inputs provided by the driver to every code quality check. -/
structure PackageCheckContext where
  srcSearchPath : System.SearchPath
  topLevelModule : Name

structure PackageCheck where
  ofFn ::
    run : PackageCheckContext → MetaM (Array Entry)

structure CheckResult where
  entries : Array Entry
  errors : Array MessageData

structure NamedPackageCheck extends PackageCheck where
  declName : Name

def getPackageCheck (declName : Name) : CoreM NamedPackageCheck := unsafe
  return { ← evalConstCheck PackageCheck ``PackageCheck declName with declName}

builtin_initialize packageCheckExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun nss => nss.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

builtin_initialize registerBuiltinAttribute {
  name := `package_code_quality_check
  descr := "Use this declaration as a check in the code quality metrics driver"
  add := fun decl _stx kind => do
    unless kind == .global do
      throwError "invalid attribute `package_code_quality_check`, must be global"
    let env ← getEnv
    let isPublic := !isPrivateName decl; let isMeta := isMarkedMeta env decl
    unless isPublic && isMeta do
      throwError "invalid attribute `package_code_quality_check`, \
        declaration `{.ofConstName decl}` must be marked as `public` and `meta`\
        {if isPublic then " but is only marked `public`" else ""}\
        {if isMeta then " but is only marked `meta`" else ""}"
    let constInfo ← getConstInfo decl
    unless ← (isDefEq constInfo.type (mkConst ``PackageCheck)).run' do
      throwError "`{.ofConstName decl}` must have type `{.ofConstName ``PackageCheck}`, got \
        `{constInfo.type}`"
    modifyEnv fun env => packageCheckExt.addEntry env decl
}

def getPackageChecks : CoreM (Array NamedPackageCheck) := do
  let mut result := #[]
  for declName in packageCheckExt.getState (← getEnv) do
    let linter ← getPackageCheck declName
    result := result.binInsert (·.declName.lt ·.declName) linter
  pure result

def runPackageChecks (checks : Array NamedPackageCheck) (ctx : PackageCheckContext) :
    CoreM CheckResult := do
  let tasks ← checks.mapM fun check => do
    let act ← Core.wrapAsync (cancelTk? := none) fun (_ : Unit) =>
      check.run ctx |>.run' Elab.Command.mkMetaContext
    return (check.declName, ← EIO.asTask (act ()))
  let mut entries := #[]
  let mut errors := #[]
  for (declName, task) in tasks do
    match task.get with
    | .ok checkEntries => entries := entries ++ checkEntries
    | .error err => errors := errors.push (s!"{declName} has failed: " ++ err.toMessageData)
  return ⟨entries, errors⟩

end Lean.Linter.CodeQuality

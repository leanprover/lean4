/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Init.System.FilePath
public import Lean.Linter.CodeQuality.Basic
public import Lean.Elab.InfoTree.Main
import Lean.CoreM
import Lean.Elab.Command

public section

open Lean Meta

namespace Lean.Linter.CodeQuality

/-!
# Code quality check registration and driver

A package code quality check is a declaration of type `PackageCheck` tagged with the
`@[package_code_quality_check]` attribute. The driver runs every registered check once
per package; each check sees the whole environment and is responsible for restricting
its metrics to the package named by the `PackageCheckContext` it receives. Registered
checks are tracked by the `packageCheckExt` environment extension and are run
concurrently, one task per check, by `runPackageChecks`, which combines all results
into a single array of entries.
-/


/-- Global inputs provided by the driver to every code quality check. -/
structure PackageCheckContext where
  pkgRoot : Name
  srcSearchPath : System.SearchPath := {}

abbrev PackageCheck := PackageCheckContext → MetaM (Array Entry)

structure NamedPackageCheck where
  declName : Name
  run : PackageCheck

def getPackageCheck (declName : Name) : CoreM PackageCheck := unsafe
  evalConstCheck PackageCheck ``PackageCheck declName

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
  (packageCheckExt.getState (← getEnv)).mapM fun declName =>
    return { declName, run := ← getPackageCheck declName }

def runPackageChecks (checks : Array NamedPackageCheck) (ctx : PackageCheckContext) :
    CoreM (Array Entry) := do
  let tasks ← checks.mapM fun check => do
    (check.declName, ·) <$> (EIO.asTask <| (← Core.wrapAsync (fun _ =>
      check.run ctx |>.run' Elab.Command.mkMetaContext
    ) (cancelTk? := none)) ())
  let mut entries := #[]
  for (declName, task) in tasks do
    match task.get with
    | .ok checkEntries => entries := entries ++ checkEntries
    | .error err =>
      IO.eprintln s!"code quality check `{declName}` failed: {← err.toMessageData.toString}"
  return entries

end Lean.Linter.CodeQuality

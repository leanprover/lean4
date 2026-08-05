/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Init.System.FilePath
public import Lean.Linter.CodeQuality.Basic
public import Lean.Linter.Init
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
into a single array of entries. A check that throws contributes no entries and is
reported back to the driver in `PackageCheckResults.failures`.
-/


/-- Global inputs provided by the driver to every code quality check. -/
structure PackageCheckContext where
  /-- Root of the package being checked. A check should report metrics only for this package. -/
  pkgRoot : Name
  /-- The package's modules that are present in the environment. -/
  modules : Array Name := #[]
  /-- The package's declarations that are present in the environment. -/
  decls : Array Name := #[]
  /-- The linter options in effect, as selected by the driver. -/
  linterOptions : LinterOptions := { toOptions := {}, linterSets := {} }
  srcSearchPath : System.SearchPath := {}

abbrev PackageCheck := PackageCheckContext → MetaM (Array Entry)

/-- The combined outcome of running a set of code quality checks. -/
structure PackageCheckResults where
  /-- The entries produced by the checks that succeeded. -/
  entries : Array Entry
  /-- The checks that threw, paired with their rendered error. -/
  failures : Array (Name × String)

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

/-- The declaration names of the registered code quality checks, in registration order. -/
def getPackageCheckNames : CoreM (Array Name) :=
  return packageCheckExt.getState (← getEnv)

/--
Runs the named code quality checks concurrently, one task per check, and combines their results.
The checks are resolved inside their own task, so a check that cannot be evaluated is reported as
an ordinary failure rather than aborting the whole run.
-/
def runPackageChecks (checkNames : Array Name) (ctx : PackageCheckContext) :
    CoreM PackageCheckResults := do
  let tasks ← checkNames.mapM fun declName => do
    let act : CoreM (Array Entry) := do
      let check ← getPackageCheck declName
      check ctx |>.run' Elab.Command.mkMetaContext
    (declName, ·) <$> (EIO.asTask <| (← Core.wrapAsync (fun _ => act) (cancelTk? := none)) ())
  let mut entries := #[]
  let mut failures := #[]
  for (declName, task) in tasks do
    match task.get with
    | .ok checkEntries => entries := entries ++ checkEntries
    | .error err => failures := failures.push (declName, ← err.toMessageData.toString)
  return { entries, failures }

end Lean.Linter.CodeQuality

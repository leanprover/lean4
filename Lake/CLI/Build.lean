/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build
import Lake.Config.Util

open Lean (Name)

namespace Lake

def resolvePkgSpec (ws : Workspace) (rootPkg : Package) (spec : String) : IO Package := do
  if spec.isEmpty then
    return rootPkg
  let pkgName := spec.toName
  if pkgName == rootPkg.name then
    return rootPkg
  if let some dep := rootPkg.dependencies.find? (·.name == pkgName) then
    LogMethodsT.run LogMethods.io <| resolveDep ws rootPkg dep
  else
    error s!"unknown package `{spec}`"

def parseTargetBaseSpec (ws : Workspace) (rootPkg : Package) (spec : String) : IO (Package × Option Name) := do
  match spec.splitOn "/" with
  | [pkgStr] =>
    return (← resolvePkgSpec ws rootPkg pkgStr, none)
  | [pkgStr, modStr] =>
    let mod := modStr.toName
    let pkg ← resolvePkgSpec ws rootPkg pkgStr
    if pkg.hasModule mod then
      return (pkg, mod)
    else
      error s!"package '{pkgStr}' has no module '{modStr}'"
  | _ =>
    error s!"invalid target spec '{spec}' (too many '/')"

def parseTargetSpec (ws : Workspace) (rootPkg : Package) (spec : String) : IO (Package × OpaqueTarget) := do
  match spec.splitOn ":" with
  | [rootSpec] =>
    let (pkg, mod?) ← parseTargetBaseSpec ws rootPkg rootSpec
    if let some mod := mod? then
      return (pkg, pkg.moduleOleanTarget mod |>.withoutInfo)
    else
      return (pkg, pkg.defaultTarget)
  | [rootSpec, facet] =>
    let (pkg, mod?) ← parseTargetBaseSpec ws rootPkg rootSpec
    if let some mod := mod? then
      if facet == "olean" then
        return (pkg, pkg.moduleOleanTarget mod |>.withoutInfo)
      else if facet == "c" then
        return (pkg, pkg.moduleOleanAndCTarget mod |>.withoutInfo)
      else if facet == "o" then
        return (pkg, pkg.moduleOTarget mod |>.withoutInfo)
      else
        error s!"unknown module facet '{facet}'"
    else
      if facet == "bin" then
        return (pkg, pkg.binTarget.withoutInfo)
      else if facet == "staticLib" then
        return (pkg, pkg.staticLibTarget.withoutInfo)
      else if facet == "sharedLib" then
        return (pkg, pkg.sharedLibTarget.withoutInfo)
      else if facet == "oleans" then
        return (pkg, pkg.oleanTarget.withoutInfo)
      else
        error s!"unknown package facet '{facet}'"
  | _ =>
    error s!"invalid target spec '{spec}' (too many ':')"

def build (targetSpecs : List String) : BuildM PUnit := do
  let pkg ← getPackage
  let targets ← liftM <| targetSpecs.mapM (parseTargetSpec (← getWorkspace) pkg)
  if targets.isEmpty then
    pkg.defaultTarget.build
  else
    targets.forM fun (pkg, t) => adaptPackage pkg <| t.build

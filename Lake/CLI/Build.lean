/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build
import Lake.CLI.Error

open Lean (Name)

namespace Lake

def Package.defaultTarget (self : Package) : OpaqueTarget :=
  match self.defaultFacet with
  | .bin => self.binTarget.withoutInfo
  | .staticLib => self.staticLibTarget.withoutInfo
  | .sharedLib => self.sharedLibTarget.withoutInfo
  | .oleans =>  self.oleanTarget.withoutInfo

def parsePkgSpec (ws : Workspace) (spec : String) : Except CliError Package :=
  if spec.isEmpty then
    return ws.root
  else
    match ws.packageByName? spec.toName with
    | some pkg => return pkg
    | none => throw <| CliError.unknownPackage spec

def parseTargetBaseSpec (ws : Workspace) (spec : String) : Except CliError (Package × Option Name) := do
  match spec.splitOn "/" with
  | [pkgStr] =>
    return (← parsePkgSpec ws pkgStr, none)
  | [pkgStr, modStr] =>
    let mod := modStr.toName
    let pkg ← parsePkgSpec ws pkgStr
    if pkg.hasModule mod then
      return (pkg, mod)
    else
      throw <| CliError.missingModule pkgStr modStr
  | _ =>
    throw <| CliError.invalidTargetSpec spec '/'

def parseTargetSpec (ws : Workspace) (spec : String) : Except CliError (BuildTarget PUnit) := do
  match spec.splitOn ":" with
  | [rootSpec] =>
    let (pkg, mod?) ← parseTargetBaseSpec ws rootSpec
    if let some mod := mod? then
      return pkg.moduleOleanTarget mod |>.withoutInfo
    else
      return pkg.defaultTarget |>.withoutInfo
  | [rootSpec, facet] =>
    let (pkg, mod?) ← parseTargetBaseSpec ws rootSpec
    if let some mod := mod? then
      if facet == "olean" then
        return pkg.moduleOleanTarget mod |>.withoutInfo
      else if facet == "c" then
        return pkg.moduleOleanAndCTarget mod |>.withoutInfo
      else if facet == "o" then
        return pkg.moduleOTarget mod |>.withoutInfo
      else
        throw <| CliError.unknownModuleFacet facet
    else
      if facet == "bin" then
        return pkg.binTarget.withoutInfo
      else if facet == "staticLib" then
        return pkg.staticLibTarget.withoutInfo
      else if facet == "sharedLib" then
        return pkg.sharedLibTarget.withoutInfo
      else if facet == "oleans" then
        return pkg.oleanTarget.withoutInfo
      else
        throw <| CliError.unknownPackageFacet  facet
  | _ =>
    throw <| CliError.invalidTargetSpec spec ':'

def parseTargetSpecs (ws : Workspace) (specs : List String) : Except CliError (List (BuildTarget PUnit)) :=
  specs.mapM <| parseTargetSpec ws

def build (targets : List (BuildTarget PUnit)) : BuildM PUnit := do
  let ws ← getWorkspace
  if targets.isEmpty then
    ws.root.defaultTarget.build
  else
    targets.forM (·.build)

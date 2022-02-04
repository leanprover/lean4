/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build
import Lake.Config.Util

open Lean (Name)

namespace Lake

def parsePkgSpec (ws : Workspace) (spec : String) : IO Package :=
  if spec.isEmpty then
    return ws.root
  else
    match ws.packageByName? spec.toName with
    | some pkg => return pkg
    | none => error s!"unknown package `{spec}`"

def parseTargetBaseSpec (ws : Workspace) (spec : String) : IO (Package × Option Name) := do
  match spec.splitOn "/" with
  | [pkgStr] =>
    return (← parsePkgSpec ws pkgStr, none)
  | [pkgStr, modStr] =>
    let mod := modStr.toName
    let pkg ← parsePkgSpec ws pkgStr
    if pkg.hasModule mod then
      return (pkg, mod)
    else
      error s!"package '{pkgStr}' has no module '{modStr}'"
  | _ =>
    error s!"invalid target spec '{spec}' (too many '/')"

def parseTargetSpec (ws : Workspace) (spec : String) : IO (BuildTarget Package) := do
  match spec.splitOn ":" with
  | [rootSpec] =>
    let (pkg, mod?) ← parseTargetBaseSpec ws rootSpec
    if let some mod := mod? then
      return pkg.moduleOleanTarget mod |>.withInfo pkg
    else
      return pkg.defaultTarget |>.withInfo pkg
  | [rootSpec, facet] =>
    let (pkg, mod?) ← parseTargetBaseSpec ws rootSpec
    if let some mod := mod? then
      if facet == "olean" then
        return pkg.moduleOleanTarget mod |>.withInfo pkg
      else if facet == "c" then
        return pkg.moduleOleanAndCTarget mod |>.withInfo pkg
      else if facet == "o" then
        return pkg.moduleOTarget mod |>.withInfo pkg
      else
        error s!"unknown module facet '{facet}'"
    else
      if facet == "bin" then
        return pkg.binTarget.withInfo pkg
      else if facet == "staticLib" then
        return pkg.staticLibTarget.withInfo pkg
      else if facet == "sharedLib" then
        return pkg.sharedLibTarget.withInfo pkg
      else if facet == "oleans" then
        return pkg.oleanTarget.withInfo pkg
      else
        error s!"unknown package facet '{facet}'"
  | _ =>
    error s!"invalid target spec '{spec}' (too many ':')"

def build (targetSpecs : List String) : BuildM PUnit := do
  let ws ← getWorkspace
  let targets ← liftM <| targetSpecs.mapM <| parseTargetSpec ws
  if targets.isEmpty then
    ws.root.defaultTarget.build
  else
    targets.forM fun t => discard <| t.build

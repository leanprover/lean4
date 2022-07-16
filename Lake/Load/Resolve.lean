/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.EStateT
import Lake.Util.StoreInsts
import Lake.Load.Package
import Lake.Load.Materialize
import Lake.Config.Workspace
import Lake.Build.Topological

open Std System

namespace Lake

/--
Resolves a `Dependency` relative to the given `Package`
in the same `Workspace`, downloading and/or updating it as necessary.
-/
def resolveDep (ws : Workspace)
(pkg : Package) (dep : Dependency) (shouldUpdate := true) : ManifestM Package := do
  let dir ← materializeDep ws.packagesDir pkg.dir dep shouldUpdate
  let depPkg ← Package.load dir dep.options
  unless depPkg.name == dep.name do
    throw <| IO.userError <|
      s!"{pkg.name} (in {pkg.dir}) depends on {dep.name}, " ++
      s!"but resolved dependency has name {depPkg.name} (in {depPkg.dir})"
  return depPkg

/--
Resolves the package's dependencies,
downloading and/or updating them as necessary.
-/
def resolveDeps (ws : Workspace) (pkg : Package)
(shouldUpdate := true) : ManifestM (NameMap Package) := do
  let resolve dep resolve := do
    let pkg ← resolveDep ws pkg dep shouldUpdate
    pkg.dependencies.forM fun dep => discard <| resolve dep
    return pkg
  let (res, map) ← EStateT.run (mkRBMap _ _ Lean.Name.quickCmp) <|
    pkg.dependencies.forM fun dep => discard <| buildTop Dependency.name resolve dep
  match res with
  | Except.ok _ => return map
  | Except.error cycle => do
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"

/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Module
import Lake.Config.Workspace

/-!
Definitions to support `lake print-paths` builds.
-/

open System
namespace Lake

/--
Construct an `Array` of `Module`s for the workspace-local modules of
a `List` of import strings.
-/
def Workspace.processImportList
(imports : List String) (self : Workspace) : Array Module := Id.run do
  let mut localImports := #[]
  for imp in imports do
    if let some mod := self.findModule? imp.toName then
      localImports := localImports.push mod
  return localImports

/--
Builds the workspace-local modules of list of imports.
Used by `lake print-paths` to build modules for the Lean server.
Returns the set of module dynlibs built (so they can be loaded by the server).

Builds only module `.olean` and `.ilean` files if the package is configured
as "Lean-only". Otherwise, also build `.c` files.
-/
def Package.buildImportsAndDeps (imports : List String) (self : Package) : BuildM (Array FilePath) := do
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    self.buildFacet &`extraDep >>= (·.buildOpaque)
    return #[]
  else
    -- build local imports from list
    let mods := (← getWorkspace).processImportList imports
    let (res, bStore) ← EStateT.run BuildStore.empty <| mods.mapM fun mod =>
      if mod.shouldPrecompile then
        buildModuleTop mod &`lean.dynlib <&> (·.withoutInfo)
      else if mod.isLeanOnly then
        buildModuleTop mod &`lean
      else
        buildModuleTop mod &`lean.c <&> (·.withoutInfo)
    let importTargets ← failOnBuildCycle res
    let dynlibTargets := bStore.collectModuleFacetArray &`lean.dynlib
    let externLibTargets := bStore.collectSharedExternLibs
    importTargets.forM (·.buildOpaque)
    let dynlibs ← dynlibTargets.mapM (·.build)
    let externLibs ← externLibTargets.mapM (·.build)
    -- Note: Lean wants the external library symbols before module symbols
    return  externLibs ++ dynlibs

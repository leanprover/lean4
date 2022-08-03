/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Index

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
def buildImportsAndDeps (imports : List String) : BuildM (Array FilePath) := do
  let ws ← getWorkspace
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    ws.root.extraDep.build >>= (·.materialize)
    return #[]
  else
    -- build local imports from list
    let mods := ws.processImportList imports
    let (importTargets, bStore) ← RecBuildM.runIn {} <| mods.mapM fun mod =>
      if mod.shouldPrecompile then
        (discard ·.toJob) <$> buildIndexTop mod.dynlib
      else
        (discard ·.toJob) <$> buildIndexTop mod.leanBin
    let dynlibJobs := bStore.collectModuleFacetArray Module.dynlibFacet
    let externLibJobs := bStore.collectSharedExternLibs
    importTargets.forM (·.await)
    -- NOTE: Unix requires the full file name of the dynlib (Windows doesn't care)
    let dynlibs ← dynlibJobs.mapM fun dynlib => do
      return FilePath.mk <| nameToSharedLib (← dynlib.await)
    let externLibs ← externLibJobs.mapM (·.await)
    -- NOTE: Lean wants the external library symbols before module symbols
    return externLibs ++ dynlibs

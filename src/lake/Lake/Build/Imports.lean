/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Index

/-!
Definitions to support `lake setup-file` builds.
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
Recursively build a set of imported modules and return their build jobs,
the build jobs of their precompiled modules and the build jobs of said modules'
external libraries.
-/
def recBuildImports (imports : Array Module)
: IndexBuildM (Array (BuildJob Unit) × Array (BuildJob Dynlib) × Array (BuildJob Dynlib)) := do
  let mut modJobs := #[]
  let mut precompileImports := OrdModuleSet.empty
  for mod in imports do
    if mod.shouldPrecompile then
      precompileImports := precompileImports.appendArray (← mod.transImports.fetch) |>.insert mod
    else
      precompileImports := precompileImports.appendArray (← mod.precompileImports.fetch)
    modJobs := modJobs.push <| ← mod.leanArts.fetch
  let pkgs := precompileImports.foldl (·.insert ·.pkg) OrdPackageSet.empty |>.toArray
  let externJobs ← pkgs.concatMapM (·.externLibs.mapM (·.dynlib.fetch))
  let precompileJobs ← precompileImports.toArray.mapM (·.dynlib.fetch)
  return (modJobs, precompileJobs, externJobs)

/--
Builds the workspace-local modules of list of imports.
Used by `lake setup-file` to build modules for the Lean server.
Returns the set of module dynlibs built (so they can be loaded by the server).

Builds only module `.olean` and `.ilean` files if the package is configured
as "Lean-only". Otherwise, also builds `.c` files.
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
    let (modJobs, precompileJobs, externLibJobs) ←
      recBuildImports mods |>.run.run
    modJobs.forM (·.await)
    let modLibs ← precompileJobs.mapM (·.await <&> (·.path))
    let externLibs ← externLibJobs.mapM (·.await <&> (·.path))
    -- NOTE: Lean wants the external library symbols before module symbols
    return externLibs ++ modLibs

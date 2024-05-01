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
Recursively build a set of imported modules and return their build jobs,
the build jobs of their precompiled modules and the build jobs of said modules'
external libraries.
-/
def recBuildImports (imports : Array Module)
: FetchM (Array (BuildJob Unit) × Array (BuildJob Dynlib) × Array (BuildJob Dynlib)) := do
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
Builds an `Array` of module imports. Used by `lake setup-file` to build modules
for the Lean server and by `lake lean` to build the imports of a file.
Returns the set of module dynlibs built (so they can be loaded by Lean).
-/
def buildImportsAndDeps (imports : Array Module) : FetchM (BuildJob (Array FilePath)) := do
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    (← getRootPackage).extraDep.fetch <&> (·.map fun _ => #[])
  else
    -- build local imports from list
    let (modJobs, precompileJobs, externLibJobs) ←
      recBuildImports imports
    let modJob ← BuildJob.mixArray modJobs
    let precompileJob ← BuildJob.collectArray precompileJobs
    let externLibJob ← BuildJob.collectArray externLibJobs
    let job ←
      modJob.bindAsync fun _ modTrace =>
      precompileJob.bindAsync fun modLibs modLibTrace =>
      externLibJob.bindSync fun externLibs externTrace => do
        -- NOTE: Lean wants the external library symbols before module symbols
        let libs := (externLibs ++ modLibs).map (·.path)
        let trace := modTrace.mix modLibTrace |>.mix externTrace
        return (libs, trace)
    return job

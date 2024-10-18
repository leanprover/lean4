/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Module

/-!
Definitions to support `lake setup-file` builds.
-/

open System
namespace Lake

/--
Builds an `Array` of module imports for a Lean file.
Used by `lake setup-file` to build modules for the Lean server and
by `lake lean` to build the imports of a file.
Returns the set of module dynlibs built (so they can be loaded by Lean).
-/
def buildImportsAndDeps (leanFile : FilePath) (imports : Array Module) : FetchM (BuildJob (Array FilePath)) := do
  withRegisterJob s!"imports ({leanFile})" do
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    (← getRootPackage).extraDep.fetch <&> (·.map fun _ => #[])
  else
    -- build local imports from list
    let modJob ← BuildJob.mixArray <| ← imports.mapM (·.olean.fetch)
    let precompileImports ← computePrecompileImportsAux leanFile imports
    let pkgs := precompileImports.foldl (·.insert ·.pkg) OrdPackageSet.empty |>.toArray
    let externLibJob ← BuildJob.collectArray <| ←
      pkgs.flatMapM (·.externLibs.mapM (·.dynlib.fetch))
    let precompileJob ← BuildJob.collectArray <| ←
      precompileImports.mapM (·.dynlib.fetch)
    let job ←
      modJob.bindAsync fun _ modTrace =>
      precompileJob.bindAsync fun modLibs modLibTrace =>
      externLibJob.bindSync fun externLibs externTrace => do
        -- NOTE: Lean wants the external library symbols before module symbols
        let libs := (externLibs ++ modLibs).map (·.path)
        let trace := modTrace.mix modLibTrace |>.mix externTrace
        return (libs, trace)
    return job

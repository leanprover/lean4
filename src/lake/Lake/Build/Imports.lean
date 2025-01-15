/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
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
def buildImportsAndDeps (leanFile : FilePath) (imports : Array Module) : FetchM (Job (Array FilePath)) := do
  withRegisterJob s!"imports ({leanFile})" do
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    (← getRootPackage).extraDep.fetch <&> (·.map fun _ => #[])
  else
    -- build local imports from list
    let modJob := Job.mixArray <| ← imports.mapM (·.olean.fetch)
    let precompileImports ← (← computePrecompileImportsAux leanFile imports).await
    let pkgs := precompileImports.foldl (·.insert ·.pkg) OrdPackageSet.empty |>.toArray
    let externLibJob := Job.collectArray <| ←
      pkgs.flatMapM (·.externLibs.mapM (·.dynlib.fetch))
    let precompileJob := Job.collectArray <| ←
      precompileImports.mapM (·.dynlib.fetch)
    let job ←
      modJob.bindM fun _ =>
      precompileJob.bindM fun modLibs =>
      externLibJob.mapM fun externLibs => do
        -- NOTE: Lean wants the external library symbols before module symbols
        return (externLibs ++ modLibs).map (·.path)
    return job

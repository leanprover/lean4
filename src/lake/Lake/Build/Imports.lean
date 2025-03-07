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
Returns the dynlibs and plugins built (so they can be loaded by Lean).
-/
def buildImportsAndDeps
  (leanFile : FilePath) (imports : Array Module)
: FetchM (Job ModuleDeps) := do
  withRegisterJob s!"setup ({leanFile})" do
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    (← getRootPackage).extraDep.fetch <&> (·.map fun _ => {})
  else
    -- build local imports from list
    let modJob := Job.mixArray <| ← imports.mapM (·.olean.fetch)
    let precompileImports ← (← computePrecompileImportsAux leanFile imports).await
    let pkgs := precompileImports.foldl (·.insert ·.pkg) OrdPackageSet.empty |>.toArray
    let externLibsJob ← fetchExternLibs pkgs
    let modLibsJob ← Job.collectArray <$>
      precompileImports.mapM (·.dynlib.fetch)
    let dynlibsJob ← (← getRootPackage).dynlibs.fetch
    let pluginsJob ← (← getRootPackage).plugins.fetch
    modJob.bindM fun _ =>
    modLibsJob.bindM fun modLibs =>
    dynlibsJob.bindM fun dynlibs =>
    pluginsJob.bindM fun plugins =>
    externLibsJob.mapM fun externLibs => do
      -- NOTE: Lean wants the external library symbols before module symbols
      let dynlibs := (externLibs ++ dynlibs).map (·.path)
      let plugins := (modLibs ++ plugins).map (·.path)
      return {dynlibs, plugins}

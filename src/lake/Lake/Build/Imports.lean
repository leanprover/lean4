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
  let root ← getRootPackage
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    root.extraDep.fetch <&> (·.map fun _ => {})
  else
    -- build local imports from list
    let modJob := Job.mixArray <| ← imports.mapM (·.olean.fetch)
    let precompileImports ← (← computePrecompileImportsAux leanFile imports).await
    let pkgs := precompileImports.foldl (·.insert ·.pkg) OrdPackageSet.empty |>.toArray
    let externLibsJob ← fetchExternLibs pkgs
    let impLibsJob ← fetchImportLibs imports
    let dynlibsJob ← root.dynlibs.fetchIn root
    let pluginsJob ← root.plugins.fetchIn root
    modJob.bindM fun _ =>
    impLibsJob.bindM fun impLibs =>
    dynlibsJob.bindM fun dynlibs =>
    pluginsJob.bindM fun plugins =>
    externLibsJob.mapM fun externLibs => do
      return computeModuleDeps impLibs externLibs dynlibs plugins

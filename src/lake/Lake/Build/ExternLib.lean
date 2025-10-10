/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Name
public import Lake.Config.FacetConfig
public import Lake.Build.Job.Monad
import Lake.Build.Job.Register
import Lake.Build.Actions
import Lake.Build.Common
import Lake.Build.Infos

/-! # External Library Build
Build function definitions for external libraries.
-/

open System

namespace Lake

private def ExternLib.recBuildStatic (lib : ExternLib) : FetchM (Job FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:static" do
  lib.config.getPath <$> fetch (lib.pkg.target lib.staticTargetName)

/-- The facet configuration for the builtin `ExternLib.staticFacet`. -/
public def ExternLib.staticFacetConfig : ExternLibFacetConfig staticFacet :=
  mkFacetJobConfig recBuildStatic

/--
Build a shared library from a static library using `leanc`
using the Lean toolchain's linker.
-/
public def buildLeanSharedLibOfStatic
  (staticLibJob : Job FilePath)
  (weakArgs traceArgs : Array String := #[])
: SpawnM (Job FilePath) :=
  staticLibJob.mapM fun staticLib => do
    addLeanTrace
    addPureTrace traceArgs
    addPlatformTrace -- shared libraries are platform-dependent artifacts
    let dynlib := staticLib.withExtension sharedLibExt
    buildFileUnlessUpToDate' dynlib do
      let lean ← getLeanInstall
      let baseArgs :=
        if System.Platform.isOSX then
          #[s!"-Wl,-force_load,{staticLib}"]
        else
          #["-Wl,--whole-archive", staticLib.toString, "-Wl,--no-whole-archive"]
      let args := baseArgs ++ weakArgs ++ traceArgs ++
        #["-L", lean.leanLibDir.toString] ++ lean.ccLinkSharedFlags
      compileSharedLib dynlib args lean.cc
    return dynlib

private def ExternLib.recBuildShared (lib : ExternLib) : FetchM (Job FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:shared" do
  buildLeanSharedLibOfStatic (← lib.static.fetch) lib.linkArgs

/-- The facet configuration for the builtin `ExternLib.sharedFacet`. -/
public def ExternLib.sharedFacetConfig : ExternLibFacetConfig sharedFacet :=
  mkFacetJobConfig recBuildShared

/-- Construct a `Dynlib` object for a shared library target. -/
def computeDynlibOfShared (sharedLibTarget : Job FilePath) : SpawnM (Job Dynlib) :=
  sharedLibTarget.mapM fun sharedLib => do
    if let some stem := sharedLib.fileStem then
      if Platform.isWindows then
        return {path := sharedLib, name := stem}
      else if stem.startsWith "lib" then
        return {path := sharedLib, name := stem.drop 3}
      else
        error s!"shared library `{sharedLib}` does not start with `lib`; this is not supported on Unix"
    else
      error s!"shared library `{sharedLib}` has no file name"

private def ExternLib.recComputeDynlib (lib : ExternLib) : FetchM (Job Dynlib) := do
  withRegisterJob s!"{lib.staticTargetName.toString}:dynlib" do
  computeDynlibOfShared (← lib.shared.fetch)

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
public def ExternLib.dynlibFacetConfig : ExternLibFacetConfig dynlibFacet :=
  mkFacetJobConfig recComputeDynlib

private def ExternLib.recBuildDefault (lib : ExternLib) : FetchM (Job FilePath) :=
  lib.static.fetch

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
public def ExternLib.defaultFacetConfig : ExternLibFacetConfig defaultFacet :=
  mkFacetJobConfig recBuildDefault (memoize := false)

/--
A name-configuration map for the initial set of
external library facets (e.g., `static`, `shared`).
-/
public def ExternLib.initFacetConfigs : DNameMap ExternLibFacetConfig :=
  DNameMap.empty
  |>.insert defaultFacet defaultFacetConfig
  |>.insert staticFacet staticFacetConfig
  |>.insert sharedFacet sharedFacetConfig
  |>.insert dynlibFacet dynlibFacetConfig

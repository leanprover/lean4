/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Common

/-! # External Library Build
Build function definitions for external libraries.
-/

open System

namespace Lake

def ExternLib.recBuildStatic (lib : ExternLib) : FetchM (Job FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:static" do
  lib.config.getPath <$> fetch (lib.pkg.target lib.staticTargetName)

/-- The facet configuration for the builtin `ExternLib.staticFacet`. -/
def ExternLib.staticFacetConfig : ExternLibFacetConfig staticFacet :=
  mkFacetJobConfig recBuildStatic

/--
Build a shared library from a static library using `leanc`
using the Lean toolchain's linker.
-/
def buildLeanSharedLibOfStatic
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
      let args := baseArgs ++ weakArgs ++ traceArgs ++ lean.ccLinkSharedFlags
      compileSharedLib dynlib args lean.cc
    return dynlib

def ExternLib.recBuildShared (lib : ExternLib) : FetchM (Job FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:shared" do
  buildLeanSharedLibOfStatic (← lib.static.fetch) lib.linkArgs

/-- The facet configuration for the builtin `ExternLib.sharedFacet`. -/
def ExternLib.sharedFacetConfig : ExternLibFacetConfig sharedFacet :=
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

def ExternLib.recComputeDynlib (lib : ExternLib) : FetchM (Job Dynlib) := do
  withRegisterJob s!"{lib.staticTargetName.toString}:dynlib" do
  computeDynlibOfShared (← lib.shared.fetch)

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
def ExternLib.dynlibFacetConfig : ExternLibFacetConfig dynlibFacet :=
  mkFacetJobConfig recComputeDynlib

def ExternLib.recBuildDefault (lib : ExternLib) : FetchM (Job FilePath) :=
  lib.static.fetch

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
def ExternLib.defaultFacetConfig : ExternLibFacetConfig defaultFacet :=
  mkFacetJobConfig recBuildDefault

/--
A name-configuration map for the initial set of
external library facets (e.g., `static`, `shared`).
-/
def ExternLib.initFacetConfigs : DNameMap ExternLibFacetConfig :=
  DNameMap.empty
  |>.insert defaultFacet defaultFacetConfig
  |>.insert staticFacet staticFacetConfig
  |>.insert sharedFacet sharedFacetConfig
  |>.insert dynlibFacet dynlibFacetConfig

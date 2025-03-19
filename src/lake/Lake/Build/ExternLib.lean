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

open System (FilePath)

namespace Lake

def ExternLib.recBuildStatic (lib : ExternLib) : FetchM (Job FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:static" do
  lib.config.getPath <$> fetch (lib.pkg.target lib.staticTargetName)

/-- The facet configuration for the builtin `ExternLib.staticFacet`. -/
def ExternLib.staticFacetConfig : ExternLibFacetConfig staticFacet :=
  mkFacetJobConfig recBuildStatic

def ExternLib.recBuildShared (lib : ExternLib) : FetchM (Job FilePath) :=
  withRegisterJob s!"{lib.staticTargetName.toString}:shared" do
  buildLeanSharedLibOfStatic (← lib.static.fetch) lib.linkArgs

/-- The facet configuration for the builtin `ExternLib.sharedFacet`. -/
def ExternLib.sharedFacetConfig : ExternLibFacetConfig sharedFacet :=
  mkFacetJobConfig recBuildShared

def ExternLib.recComputeDynlib (lib : ExternLib) : FetchM (Job Dynlib) := do
  withRegisterJob s!"{lib.staticTargetName.toString}:dynlib" do
  computeDynlibOfShared (← lib.shared.fetch)

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
def ExternLib.dynlibFacetConfig : ExternLibFacetConfig dynlibFacet :=
  mkFacetJobConfig recComputeDynlib

/--
A name-configuration map for the initial set of
external library facets (e.g., `static`, `shared`).
-/
def ExternLib.initFacetConfigs : DNameMap ExternLibFacetConfig :=
  DNameMap.empty
  |>.insert staticFacet staticFacetConfig
  |>.insert sharedFacet sharedFacetConfig
  |>.insert dynlibFacet dynlibFacetConfig

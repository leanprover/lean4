/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Common
import Lake.Config.InputFile

/-! # Input File Build
Build function definitions for input files and directories.
-/

open System (FilePath)

namespace Lake

/-! ## Input File -/

private def InputFile.recFetch (t : InputFile) : FetchM (Job FilePath) :=
  withRegisterJob s!"{t.name}" do
  inputFile t.path t.text

/-- The facet configuration for the builtin `ExternLib.staticFacet`. -/
def InputFile.defaultFacetConfig : KFacetConfig InputFile.facetKind defaultFacet :=
  mkFacetJobConfig recFetch

/--
A name-configuration map for the initial set of
input file facets (e.g., `default`).
-/
def InputFile.initFacetConfigs : DNameMap (KFacetConfig InputFile.facetKind) :=
  DNameMap.empty
  |>.insert defaultFacet defaultFacetConfig

/-! ## Input Directory -/

private def InputDir.recFetch (t : InputDir) : FetchM (Job (Array FilePath)) :=
  withRegisterJob s!"{t.name}" do
  inputDir t.path t.text t.filter

/-- The facet configuration for the builtin `ExternLib.staticFacet`. -/
def InputDir.defaultFacetConfig : KFacetConfig InputDir.facetKind defaultFacet :=
  mkFacetJobConfig recFetch

/--
A name-configuration map for the initial set of
input directory facets (e.g., `default`).
-/
def InputDir.initFacetConfigs : DNameMap (KFacetConfig InputDir.facetKind) :=
  DNameMap.empty
  |>.insert defaultFacet defaultFacetConfig

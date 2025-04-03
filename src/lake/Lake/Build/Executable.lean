/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Common

namespace Lake
open System (FilePath)

/-! # Lean Executable Build
The build function definition for a Lean executable.
-/

def LeanExe.recBuildExe (self : LeanExe) : FetchM (Job FilePath) :=
  withRegisterJob s!"{self.name}" do
  /-
  Remark: We must build the root before we fetch the transitive imports
  so that errors in the import block of transitive imports will not kill this
  job before the root is built.
  -/
  let mut objJobs := #[]
  let mut libJobs := #[]
  let shouldExport := self.supportInterpreter
  for facet in self.root.nativeFacets shouldExport do
    objJobs := objJobs.push <| ← facet.fetch self.root
  let imports ← (← self.root.transImports.fetch).await
  for mod in imports do
    for facet in mod.nativeFacets shouldExport do
      objJobs := objJobs.push <| ← facet.fetch mod
  let libs := imports.foldl (·.insert ·.lib) OrdHashSet.empty |>.toArray
  for lib in libs do
    for link in lib.moreLinkObjs do
      objJobs := objJobs.push <| ← link.fetchIn lib.pkg
    for link in lib.moreLinkLibs do
      libJobs := libJobs.push <| ← link.fetchIn lib.pkg
  let deps := (← (← self.pkg.transDeps.fetch).await).push self.pkg
  for dep in deps do
    for lib in dep.externLibs do
      objJobs := objJobs.push <| ← lib.static.fetch
  buildLeanExe self.file objJobs libJobs self.weakLinkArgs self.linkArgs self.sharedLean

/-- The facet configuration for the builtin `LeanExe.exeFacet`. -/
def LeanExe.exeFacetConfig : LeanExeFacetConfig exeFacet :=
  mkFacetJobConfig recBuildExe

def LeanExe.recBuildDefault (lib : LeanExe) : FetchM (Job FilePath) :=
  lib.exe.fetch

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
def LeanExe.defaultFacetConfig : LeanExeFacetConfig defaultFacet :=
  mkFacetJobConfig recBuildDefault

/--
A name-configuration map for the initial set of
Lean executable facets (e.g., `exe`).
-/
def LeanExe.initFacetConfigs : DNameMap LeanExeFacetConfig :=
  DNameMap.empty
  |>.insert defaultFacet defaultFacetConfig
  |>.insert exeFacet exeFacetConfig

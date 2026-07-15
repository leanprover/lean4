/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.FacetConfig
import Lake.Build.Job.Register
import Lake.Build.Target.Fetch
import Lake.Build.Common
import Lake.Build.Infos

namespace Lake
open System (FilePath)

/-! # Lean Executable Build
The build function definition for a Lean executable.
-/

def LeanExe.recBuildExe (self : LeanExe) : FetchM (Job FilePath) :=
  withRegisterJob s!"{self.name}:exe" <| withCurrPackage self.pkg do
  let infoJob ←
    if self.supportInterpreter
    then self.root.linkInfoExport.fetch
    else self.root.linkInfoNoExport.fetch
  infoJob.mapM fun info => do
    let args := self.exeOnlyLinkArgs ++ info.args
    addPureTrace self.exeOnlyLinkArgs "LeanExe.exeOnlyLinkArgs"
    buildLeanExeSync self.file info.objs info.libs args self.sharedLean

/-- The facet configuration for the builtin `LeanExe.exeFacet`. -/
public def LeanExe.exeFacetConfig : LeanExeFacetConfig exeFacet :=
  mkFacetJobConfig recBuildExe

def LeanExe.recBuildDefault (lib : LeanExe) : FetchM (Job FilePath) :=
  lib.exe.fetch

/-- The facet configuration for the builtin `ExternLib.dynlibFacet`. -/
public def LeanExe.defaultFacetConfig : LeanExeFacetConfig defaultFacet :=
  mkFacetJobConfig recBuildDefault (memoize := false)

/--
A name-configuration map for the initial set of
Lean executable facets (e.g., `exe`).
-/
public def LeanExe.initFacetConfigs : DNameMap LeanExeFacetConfig :=
  DNameMap.empty
  |>.insert defaultFacet defaultFacetConfig
  |>.insert exeFacet exeFacetConfig

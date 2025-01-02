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
  let mut linkJobs := #[]
  for facet in self.root.nativeFacets self.supportInterpreter do
    linkJobs := linkJobs.push <| ← fetch <| self.root.facet facet.name
  let imports ← (← self.root.transImports.fetch).await
  for mod in imports do
    for facet in mod.nativeFacets self.supportInterpreter do
      linkJobs := linkJobs.push <| ← fetch <| mod.facet facet.name
  let deps := (← (← fetch <| self.pkg.facet `deps).await).push self.pkg
  for dep in deps do for lib in dep.externLibs do
    linkJobs := linkJobs.push <| ← lib.static.fetch
  buildLeanExe self.file linkJobs self.weakLinkArgs self.linkArgs self.sharedLean

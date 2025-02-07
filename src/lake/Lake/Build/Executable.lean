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
  let linkJobs ← (self.root.nativeFacets self.supportInterpreter).mapM fun facet =>
    (self.root.facet facet.name).fetch
  (← self.root.transImports.fetch).bindM fun imports => do
  let linkJobs ← imports.foldlM (init := linkJobs) fun linkJobs mod => do
    (mod.nativeFacets self.supportInterpreter).foldlM (init := linkJobs) fun linkJobs facet =>
      linkJobs.push <$> (mod.facet facet.name).fetch
  (← self.pkg.transDeps.fetch).bindM fun deps => do
  let linkJobs ← (deps.push self.pkg).foldlM (init := linkJobs) fun linkJobs dep =>
    dep.externLibs.foldlM (init := linkJobs) fun linkJobs lib => do
      linkJobs.push <$> lib.static.fetch
  buildLeanExe self.file linkJobs self.weakLinkArgs self.linkArgs self.sharedLean

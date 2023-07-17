/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Common

namespace Lake

/-- Get the Lean executable in the workspace with the configuration's name. -/
@[inline] def LeanExeConfig.get (self : LeanExeConfig)
[Monad m] [MonadError m] [MonadLake m] : m LeanExe := do
  let some exe ← findLeanExe? self.name
    | error "Lean executable '{self.name}' does not exist in the workspace"
  return exe


/-- Fetch the build of the Lean executable. -/
@[inline] def LeanExeConfig.fetch
(self : LeanExeConfig) : IndexBuildM (BuildJob FilePath) := do
  (← self.get).exe.fetch

/-! # Build Executable -/

protected def LeanExe.recBuildExe
(self : LeanExe) : IndexBuildM (BuildJob FilePath) := do
  let imports ← self.root.transImports.fetch
  let mut linkJobs := #[← self.root.o.fetch]
  for mod in imports do for facet in mod.nativeFacets do
    linkJobs := linkJobs.push <| ← fetch <| mod.facet facet.name
  let deps := (← fetch <| self.pkg.facet `deps).push self.pkg
  for dep in deps do for lib in dep.externLibs do
    linkJobs := linkJobs.push <| ← lib.static.fetch
  buildLeanExe self.file linkJobs self.linkArgs

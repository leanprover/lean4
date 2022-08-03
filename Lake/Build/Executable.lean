/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Common

namespace Lake

/-! # Build Executable -/

protected def LeanExe.recBuildExe
(self : LeanExe) : IndexBuildM (BuildJob FilePath) := do
  let (_, imports) ← self.root.imports.recBuild
  let linkJobs := #[← self.root.o.recBuild]
  let mut linkJobs ← imports.foldlM (init := linkJobs) fun arr mod => do
    let mut arr := arr
    for facet in mod.nativeFacets do
      arr := arr.push <| ← recBuild <| mod.facet facet.name
    return arr
  let deps := (← recBuild <| self.pkg.facet `deps).push self.pkg
  for dep in deps do for lib in dep.externLibs do
    linkJobs := linkJobs.push <| ← lib.static.recBuild
  buildLeanExe self.file linkJobs self.linkArgs

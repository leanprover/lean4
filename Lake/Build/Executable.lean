/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Targets

namespace Lake

/-! # Build Executable -/

protected def LeanExe.recBuildExe
(self : LeanExe) : IndexBuildM (BuildJob FilePath) := do
  let (_, imports) ← self.root.imports.recBuild
  let linkTargets := #[Target.active <| ← self.root.o.recBuild]
  let mut linkTargets ← imports.foldlM (init := linkTargets) fun arr mod => do
    let mut arr := arr
    for facet in mod.nativeFacets do
      arr := arr.push <| Target.active <| ← recBuild <| mod.facet facet.name
    return arr
  let deps := (← recBuild <| self.pkg.facet `deps).push self.pkg
  for dep in deps do for lib in dep.externLibs do
    linkTargets := linkTargets.push <| Target.active <| ← lib.static.recBuild
  leanExeTarget self.name.toString self.file linkTargets self.linkArgs |>.activate
